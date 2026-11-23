(in-package #:sat-protocol/conformance)

;;; 0.2 MINIMIZE :STRATEGY (L2b-1): every strategy reaches the brute-force
;;; optimum and proves it (OPTIMAL-P T). Lexicographic objectives: lex-test;
;;; budgets and hints: minimize-budget-test; chains: chain-test.

(defun check-optimum (label expected model cost optimal-p model-ok-p model-cost)
  "Shared assertions: COST = EXPECTED; for a model, OPTIMAL-P T, MODEL valid
(MODEL-OK-P) and of the reported cost (MODEL-COST)."
  (ok (equal expected cost) (format nil "~A: optimum ~S, got ~S" label expected cost))
  (when model
    (ok (eq t optimal-p) (format nil "~A: proven optimal" label))
    (ok (funcall model-ok-p model) (format nil "~A: model satisfies the formula" label))
    (ok (equal cost (funcall model-cost model)) (format nil "~A: model has the reported cost" label))))

(deftest-parametrize strategy-random-cnf
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; Random 3-SAT over 8 variables (some UNSAT), objectives with repeated and
  ;; complementary literals and diverse weights (strata).
  (let ((rng (make-rng 31)) (sat 0) (unsat 0))
    (dotimes (i 14)
      (let* ((clauses (random-3sat rng 8 (+ 18 (rng-int rng 24))))
             (objective (random-int-objective rng 8 (+ 3 (rng-int rng 6)) '(1 1 2 3 5 8 20)))
             (best (brute-optimum clauses 8 objective)))
        (if best (incf sat) (incf unsat))
        (multiple-value-bind (model cost optimal-p)
            (minimize (clauses->cnf clauses 8) (int-objective->literals objective)
                      :strategy strategy)
          (check-optimum (format nil "~A instance ~D" strategy i) best model cost optimal-p
                         (lambda (m) (clauses-satisfied-p clauses (model->assignment m)))
                         (lambda (m) (int-cost objective (model->assignment m)))))))
    (ok (and (plusp sat) (plusp unsat)) "both outcomes exercised")))

(deftest-parametrize strategy-random-formulas
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; Non-clausal formulas: Tseitin auxiliaries are in the CNF but never in the
  ;; objective. Objective names may be absent from the formula.
  (let ((rng (make-rng 41)) (names '("p" "q" "r" "s" "t")))
    (dotimes (i 14)
      (let* ((sexp (random-sexp rng names 3))
             (objective (random-name-objective rng names (+ 2 (rng-int rng 5)) '(1 2 3 4 10)))
             (best (sexp-optimum sexp names objective)))
        (multiple-value-bind (model cost optimal-p)
            (minimize (f sexp) objective :strategy strategy)
          (check-optimum (format nil "~A formula ~D" strategy i) best model cost optimal-p
                         (lambda (m) (sexp-eval sexp m))
                         (lambda (m) (name-cost objective m))))))))

(deftest-parametrize strategy-small-cases
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (testing "the 0.1 cheapest case"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b" "c")) (list (cons 3 "a") (cons 1 "b") (cons 2 "c"))
                  :strategy strategy)
      (ok (eql 1 cost))
      (ok (eq t optimal-p))
      (ok (equal '(("a" . nil) ("b" . t) ("c" . nil)) model))))
  (testing "forced cost"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:and "a" (:or "b" "c"))) (list (cons 5 "a") (cons 2 "b") (cons 2 "c"))
                  :strategy strategy)
      (ok (eql 7 cost))
      (ok (eq t optimal-p))
      (ok (= 3 (length model)) "complete model")))
  (testing "unsatisfiable: exactly two values"
    (ok (equal '(nil nil)
               (multiple-value-list
                (minimize (f '(:and "a" (:not "a"))) (list (cons 1 "a")) :strategy strategy)))))
  (testing "empty objective"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b")) nil :strategy strategy)
      (ok (eql 0 cost))
      (ok (eq t optimal-p))
      (ok (sexp-eval '(:or "a" "b") model))))
  (testing "assumptions"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b")) (list (cons 1 "a") (cons 1 "b"))
                  :assumptions '("a" "b") :strategy strategy)
      (ok (eql 2 cost))
      (ok (eq t optimal-p))
      (ok (equal '(("a" . t) ("b" . t)) model))))
  (testing "weight 0, repeated and complementary entries"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b"))
                  (list (cons 0 "b") (cons 1 "a") (cons 2 "a") (cons 3 (sat-not (sat-var "a"))))
                  :strategy strategy)
      (ok (eql 3 cost) "a costs 3 either way")
      (ok (eq t optimal-p))
      (ok (sexp-eval '(:or "a" "b") model))))
  (testing "a new variable in the objective"
    (multiple-value-bind (model cost) (minimize (f "a") (list (cons 4 "z")) :strategy strategy)
      (ok (eql 0 cost))
      (ok (equal '(("a" . t) ("z" . nil)) model))))
  (testing "strata: one heavy entry outweighs many light ones"
    ;; Each clause needs h or its l_i: h true costs 100, h false costs 4.
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:and (:or "h" "l1") (:or "h" "l2") (:or "h" "l3") (:or "h" "l4")))
                  (list (cons 100 "h") (cons 1 "l1") (cons 1 "l2") (cons 1 "l3") (cons 1 "l4"))
                  :strategy strategy)
      (ok (eql 4 cost))
      (ok (eq t optimal-p))
      (ok (equal '(nil t) (multiple-value-list (model-value model "h")))))))

(deftest strategy-default-is-linear-bdd
  ;; Same search, same answer: the default and an explicit :LINEAR-BDD agree
  ;; on model and cost (the 0.1 behaviour).
  (let ((rng (make-rng 52)))
    (dotimes (i 6)
      (let* ((clauses (random-3sat rng 7 20))
             (objective (int-objective->literals (random-int-objective rng 7 5 '(1 2 3))))
             (cnf (clauses->cnf clauses 7)))
        (ok (equal (multiple-value-list (minimize cnf objective))
                   (multiple-value-list (minimize cnf objective :strategy :linear-bdd)))
            (format nil "instance ~D" i))))))

(deftest strategy-bad-value
  (ok (signals (minimize (f "a") (list (cons 1 "a")) :strategy :nope) 'type-error))
  (ok (signals (minimize (f "a") (list (cons 1 "a")) :strategy nil) 'type-error)))
