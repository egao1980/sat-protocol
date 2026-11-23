(in-package #:sat-protocol/conformance)

;;; The weighted chain family (optimum.lisp): one-hot choices per position,
;;; no-goods and soft costs between adjacent positions, checked against the
;;; dynamic-programming oracle CHAIN-DP. This is the shape of weighted
;;; sequence-labelling / chain-structured selection problems, kept small
;;; enough for a DPLL backend to prove optimality.

(defun check-chain-optimum (label chain model cost optimal-p &key (level-costs nil))
  "COST equals the DP optimum (a list for :lex when LEVEL-COSTS), MODEL is a
valid labelling of that cost, OPTIMAL-P is T."
  (let ((dp (chain-dp chain)))
    (ok (equal (if level-costs dp (first dp)) cost) (format nil "~A: DP optimum ~S" label dp))
    (when dp
      (ok (eq t optimal-p) (format nil "~A: proven" label))
      (let ((labelling (chain-model-labelling chain model)))
        (ok (not (eq :invalid labelling)) (format nil "~A: one label per position, no no-good" label))
        (unless (eq :invalid labelling)
          (ok (equal (if level-costs
                         (chain-labelling-cost chain labelling)
                         (first (chain-labelling-cost chain labelling)))
                     cost)
              (format nil "~A: the labelling has the reported cost" label)))))))

(deftest chain-oracle-self-check
  ;; The DP oracle against enumeration of every labelling (plain and :lex).
  (let ((feasible 0) (infeasible 0))
    (dolist (levels '(1 2))
      (dolist (c (random-chains (+ 90 levels) 30 :positions 4 :max-labels 3
                                                 :levels levels :nogood-percent 35))
        (let ((dp (chain-dp c)))
          (if dp (incf feasible) (incf infeasible))
          (ok (equal (chain-brute c) dp)))))
    (ok (and (plusp feasible) (plusp infeasible)) "both outcomes exercised")))

(deftest chain-formula-is-clause-shaped
  ;; The hint and budget tests rely on it: TO-CNF adds no auxiliary.
  (dolist (c (random-chains 93 5 :positions 4))
    (let ((cnf (to-cnf (chain-formula c))))
      (ok (notany (lambda (i) (cnf-aux-variable-p cnf i))
                  (loop for i from 1 to (cnf-variable-count cnf) collect i))))))

(deftest-parametrize chain-minimize
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  ;; 14 chains of 2 to 5 positions, 2 or 3 labels each.
  (let ((n 0))
    (dolist (spec '((2 2 3 4) (3 2 3 4) (4 2 3 4) (5 2 3 2)))
      (destructuring-bind (positions min-labels max-labels count) spec
        (dolist (c (random-chains (+ 100 positions) count :positions positions
                                                          :min-labels min-labels
                                                          :max-labels max-labels
                                                          :nogood-percent 25))
          (multiple-value-bind (model cost optimal-p)
              (minimize (chain-formula c) (chain-objective c) :strategy strategy)
            (check-chain-optimum (format nil "~A chain ~D" strategy (incf n))
                                 c model cost optimal-p)))))
    (ok (= 14 n))))

(deftest-parametrize chain-infeasible
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let ((c (random-chain (make-rng 5) :positions 3 :nogood-percent 100)))
    (ok (null (chain-dp c)))
    (ok (equal '(nil nil)
               (multiple-value-list
                (minimize (chain-formula c) (chain-objective c) :strategy strategy))))))

(deftest-parametrize chain-exactly-one-encodings
    ((encoding)
     :ids ("auto" "pairwise" "sequential" "totalizer" "bdd")
     (:auto) (:pairwise) (:sequential) (:totalizer) (:bdd))
  ;; The one-hot constraint through SAT-EXACTLY-ONE, minimised with the default
  ;; strategy and with :CORE-GUIDED.
  (let ((n 0))
    (dolist (c (random-chains 110 4 :positions 3 :min-labels 3 :max-labels 4))
      (dolist (strategy '(:linear-bdd :core-guided))
        (multiple-value-bind (model cost optimal-p)
            (minimize (chain-formula c :encoding encoding) (chain-objective c) :strategy strategy)
          (check-chain-optimum (format nil "~A/~A chain ~D" encoding strategy (incf n))
                               c model cost optimal-p))))))

(deftest-parametrize chain-lex
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let ((n 0))
    (dolist (c (random-chains 120 6 :positions 3 :levels 2))
      (multiple-value-bind (model cost optimal-p)
          (minimize (chain-formula c) (chain-lex-objective c) :strategy strategy)
        (check-chain-optimum (format nil "~A lex chain ~D" strategy (incf n))
                             c model cost optimal-p :level-costs t)))))
