(in-package #:sat-protocol/conformance)

;;; 0.2 MINIMIZE :BUDGET (decisions over all calls), :TIMEOUT (seconds), :HINT
;;; and OPTIMAL-P, for every strategy. The deterministic cases follow from the
;;; rules in sat-protocol's minimize.lisp: the first call assumes the hint; a
;;; complete hint on a clause-shaped formula needs no decision; no call starts
;;; once the budget is spent.

(defun hint-chains ()
  "Clause-shaped chains whose worst feasible labelling costs more than the
optimum (so a complete hint of it is a non-optimal incumbent)."
  (remove-if-not (lambda (c)
                   (let ((worst (chain-worst-labelling c)))
                     (and worst (lex< (chain-dp c) (chain-labelling-cost c worst)))))
                 (random-chains 77 8 :positions 3 :max-labels 3 :levels 1)))

(defun model-agrees-p (model hint)
  "MODEL binds every name of HINT ((name . boolean) ...) to the same value."
  (every (lambda (pair)
           (equal (list (cdr pair) t) (multiple-value-list (model-value model (car pair)))))
         hint))

(defun check-chain-result (label chain model cost optimal-p)
  "MODEL is a valid labelling of CHAIN, COST its objective cost, and OPTIMAL-P
T only when COST is the DP optimum."
  (let ((optimum (first (chain-dp chain))))
    (ok (not (eq :invalid (chain-model-labelling chain model))) (format nil "~A: valid labelling" label))
    (ok (eql cost (name-cost (chain-objective chain) model)) (format nil "~A: reported cost" label))
    (ok (<= optimum cost) (format nil "~A: never below the optimum" label))
    (when optimal-p
      (ok (eql optimum cost) (format nil "~A: OPTIMAL-P T only at the optimum" label)))))

(deftest-parametrize budget-zero-complete-hint
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let ((chains (hint-chains)))
    (ok (<= 3 (length chains)) "enough fixtures")
    (dolist (c chains)
      (let* ((worst (chain-worst-labelling c))
             (hint (chain-model c worst)))
        (dolist (limit '((:budget 0) (:timeout 0)))
          (multiple-value-bind (model cost optimal-p)
              (apply #'minimize (chain-formula c) (chain-objective c)
                     :strategy strategy :hint hint limit)
            (ok (model-agrees-p model hint) (format nil "~S: the hint is the answer" limit))
            (ok (eql (first (chain-labelling-cost c worst)) cost) (format nil "~S: its cost" limit))
            (ok (null optimal-p) (format nil "~S: not proven" limit))))))))

(deftest-parametrize budget-zero-hint-of-cost-zero
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (ok (equal '((("a" . nil) ("b" . t)) 0 t)
             (multiple-value-list
              (minimize (f '(:or "a" "b")) (list (cons 1 "a"))
                        :strategy strategy :budget 0 :hint '(("a" . nil) ("b" . t)))))
      "an incumbent of cost 0 is optimal without a further call"))

(deftest-parametrize budget-zero-without-model-signals
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let* ((c (first (hint-chains)))
         (formula (chain-formula c))
         (objective (chain-objective c)))
    (ok (signals (minimize formula objective :strategy strategy :budget 0) 'sat-budget-exceeded))
    (ok (equal '(0 nil)
               (handler-case (minimize formula objective :strategy strategy :budget 0)
                 (sat-budget-exceeded (e)
                   (list (sat-budget-exceeded-budget e) (sat-budget-exceeded-timeout e)))))
        "the decision budget ran out")
    (ok (equal '(nil 0)
               (handler-case (minimize formula objective :strategy strategy :timeout 0)
                 (sat-budget-exceeded (e)
                   (list (sat-budget-exceeded-budget e) (sat-budget-exceeded-timeout e)))))
        "the timeout ran out")
    (ok (equal '(:gave-up nil)
               (handler-bind ((sat-budget-exceeded (lambda (e) (use-value :gave-up e))))
                 (multiple-value-list (minimize formula objective :strategy strategy :budget 0))))
        "USE-VALUE")
    (let ((signals 0))
      (multiple-value-bind (model cost optimal-p)
          (handler-bind ((sat-budget-exceeded (lambda (e) (incf signals) (continue e))))
            (minimize formula objective :strategy strategy :budget 0))
        (ok (plusp signals))
        (ok model "CONTINUE goes on until a model is found")
        (when model
          (check-chain-result "continue" c model cost optimal-p))))))

(deftest-parametrize budget-unsat-within-budget
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; Refuted without a decision: UNSAT is an answer, not an exhausted budget.
  (ok (equal '(nil nil)
             (multiple-value-list
              (minimize (f '(:and "a" (:not "a"))) (list (cons 1 "a"))
                        :strategy strategy :budget 0)))))

(deftest-parametrize budget-large-is-unbudgeted
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (dolist (c (hint-chains))
    (multiple-value-bind (model cost optimal-p)
        (minimize (chain-formula c) (chain-objective c)
                  :strategy strategy :budget 1000000 :timeout 600)
      (ok (eql (first (chain-dp c)) cost))
      (ok (eq t optimal-p))
      (check-chain-result "large budget" c model cost optimal-p))))

(deftest-parametrize budget-sweep-anytime
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; Budgets 0..24: no model yet (signal), a best-so-far (OPTIMAL-P NIL) or a
  ;; proven optimum. With the budget the first call needed, no further call
  ;; starts, so some budget returns an unproven incumbent.
  (let ((unproven 0) (proven 0) (none 0))
    (dolist (c (subseq (hint-chains) 0 4))
      (loop for budget from 0 to 24
            do (multiple-value-bind (model cost optimal-p)
                   (handler-case (minimize (chain-formula c) (chain-objective c)
                                           :strategy strategy :budget budget)
                     (sat-budget-exceeded () (values :no-model nil nil)))
                 (cond ((eq model :no-model) (incf none))
                       (t (if optimal-p (incf proven) (incf unproven))
                          (check-chain-result (format nil "budget ~D" budget)
                                              c model cost optimal-p))))))
    (ok (plusp none) "small budgets find no model")
    (ok (plusp unproven) "some budget returns an unproven incumbent")))

(deftest-parametrize budget-shared-by-lex-levels
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let ((chains (remove-if-not (lambda (c)
                                 (let ((worst (chain-worst-labelling c)))
                                   (lex< (chain-dp c) (chain-labelling-cost c worst))))
                               (remove nil (random-chains 78 6 :positions 3 :levels 2)
                                       :key #'chain-dp))))
    (ok (plusp (length chains)))
    (dolist (c chains)
      (let* ((worst (chain-worst-labelling c))
             (hint (chain-model c worst)))
        (multiple-value-bind (model cost optimal-p)
            (minimize (chain-formula c) (chain-lex-objective c)
                      :strategy strategy :budget 0 :hint hint)
          (ok (model-agrees-p model hint))
          (ok (equal (chain-labelling-cost c worst) cost) "the hint's cost at every level")
          (ok (null optimal-p)))))))

(deftest-parametrize hint-partial-and-inconsistent
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (dolist (c (hint-chains))
    (let* ((worst (chain-worst-labelling c))
           (x-only (loop for p from 0 for l in worst collect (sat-var (chain-x p l))))
           (clash (list (cons (chain-x 0 0) t) (cons (chain-x 0 1) t))))
      (dolist (hint (list x-only clash))
        (multiple-value-bind (model cost optimal-p)
            (minimize (chain-formula c) (chain-objective c) :strategy strategy :hint hint)
          (ok (eql (first (chain-dp c)) cost) "the hint does not change the optimum")
          (ok (eq t optimal-p))
          (check-chain-result "hint" c model cost optimal-p))))))

(deftest-parametrize order-phase-with-strategies
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (dolist (c (hint-chains))
    (dolist (args (list (list :phase :false)
                        (list :phase :true :order (lambda (names) (car (last names))))
                        (list :order #'first :phase (lambda (name) (eq :y (first name))))))
      (multiple-value-bind (model cost optimal-p)
          (apply #'minimize (chain-formula c) (chain-objective c) :strategy strategy args)
        (ok (eql (first (chain-dp c)) cost))
        (ok (eq t optimal-p))
        (check-chain-result "order/phase" c model cost optimal-p)))))

(deftest minimize-argument-errors
  (let ((formula (f '(:or "a" "b"))) (objective (list (cons 1 "a"))))
    (ok (signals (minimize formula objective :budget -1) 'type-error))
    (ok (signals (minimize formula objective :budget 1.5) 'type-error))
    (ok (signals (minimize formula objective :timeout -1) 'type-error))
    (ok (signals (minimize formula objective :timeout :soon) 'type-error))
    (ok (signals (minimize formula objective :hint (list (f '(:and "a" "b")))) 'sat-invalid-formula))
    (ok (signals (minimize formula objective :hint (list nil)) 'sat-invalid-formula))
    (ok (signals (minimize formula objective :phase :sideways) 'sat-error))
    (ok (signals (minimize formula objective :order (constantly "nope")) 'sat-error))))

(deftest minimize-hint-forms
  ;; Literal formulas, bare names and (name . value) conses may be mixed.
  (multiple-value-bind (model cost optimal-p)
      (minimize (f '(:or "a" "b" "c")) (list (cons 3 "a") (cons 1 "b") (cons 2 "c"))
                :hint (list "a" (sat-not (sat-var "b")) (cons "c" nil)))
    (ok (eql 1 cost))
    (ok (eq t optimal-p))
    (ok (equal '(("a" . nil) ("b" . t) ("c" . nil)) model)))
  (multiple-value-bind (model cost)
      (minimize (f "a") (list (cons 1 "a")) :hint (list (cons "new" t)))
    (ok (eql 1 cost))
    (ok (equal '(t t) (multiple-value-list (model-value model "new")))
        "a variable first seen in the hint is a free user variable")))
