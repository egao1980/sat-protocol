(in-package #:sat-protocol/conformance)

;;; 0.2 lexicographic objectives (:lex O1 ... On): COST is a list of per-level
;;; costs, optimal lexicographically, for every strategy.

(deftest-parametrize lex-small
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (testing "level order decides"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b")) (list :lex (list (cons 1 "a")) (list (cons 1 "b")))
                  :strategy strategy)
      (ok (equal '(0 1) cost))
      (ok (eq t optimal-p))
      (ok (equal '(("a" . nil) ("b" . t)) model)))
    (multiple-value-bind (model cost)
        (minimize (f '(:or "a" "b")) (list :lex (list (cons 1 "b")) (list (cons 1 "a")))
                  :strategy strategy)
      (ok (equal '(0 1) cost))
      (ok (equal '(("a" . t) ("b" . nil)) model))))
  (testing "not a weighted sum: level 1 wins whatever level 2 costs"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "c")) (list :lex (list (cons 1 "a")) (list (cons 10 "c")))
                  :strategy strategy)
      (ok (equal '(0 10) cost))
      (ok (eq t optimal-p))
      (ok (equal '(nil t) (multiple-value-list (model-value model "a"))))))
  (testing "one level: a list of one cost"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b")) (list :lex (list (cons 2 "a") (cons 3 "b")))
                  :strategy strategy)
      (ok (equal '(2) cost))
      (ok (eq t optimal-p))
      (ok (sexp-eval '(:or "a" "b") model))))
  (testing "a literal in several levels; an empty level"
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b"))
                  (list :lex (list (cons 1 "a")) nil (list (cons 2 "a") (cons 1 "b")))
                  :strategy strategy)
      (ok (equal '(0 0 1) cost))
      (ok (eq t optimal-p))
      (ok (equal '(("a" . nil) ("b" . t)) model))))
  (testing "unsatisfiable: exactly two values"
    (ok (equal '(nil nil)
               (multiple-value-list
                (minimize (f '(:and "a" (:not "a")))
                          (list :lex (list (cons 1 "a")) (list (cons 1 "b")))
                          :strategy strategy)))))
  (testing "a fresh cost list"
    (let ((objective (list :lex (list (cons 1 "a")) (list (cons 1 "b")))))
      (let ((cost (nth-value 1 (minimize (f '(:or "a" "b")) objective :strategy strategy))))
        (setf (first cost) 99))
      (ok (equal '(0 1) (nth-value 1 (minimize (f '(:or "a" "b")) objective :strategy strategy)))))))

(deftest-parametrize lex-random-against-brute-force
    ((strategy)
     :ids ("linear-bdd" "linear-totalizer" "stratified" "core-guided")
     (:linear-bdd) (:linear-totalizer) (:stratified) (:core-guided))
  (let ((rng (make-rng 61)) (checked 0))
    (dotimes (i 10)
      (let* ((clauses (random-3sat rng 7 (+ 12 (rng-int rng 14))))
             (levels (loop repeat (+ 2 (rng-int rng 2))
                           collect (random-int-objective rng 7 (+ 2 (rng-int rng 3)) '(1 2 3 5))))
             (best (brute-lex-optimum clauses 7 levels)))
        (multiple-value-bind (model cost optimal-p)
            (minimize (clauses->cnf clauses 7)
                      (cons :lex (mapcar #'int-objective->literals levels))
                      :strategy strategy)
          (ok (equal best cost) (format nil "~A instance ~D: ~S" strategy i best))
          (when model
            (incf checked)
            (ok (eq t optimal-p))
            (ok (clauses-satisfied-p clauses (model->assignment model)))
            (ok (equal cost (mapcar (lambda (o) (int-cost o (model->assignment model))) levels))
                "COST is the model's cost at every level")))))
    (ok (plusp checked))))

(deftest lex-bad-objectives
  (ok (signals (minimize (f "a") (list :lex)) 'type-error) "no level")
  (ok (signals (minimize (f "a") (list :lex 3)) 'type-error) "a level that is not a list")
  (ok (signals (minimize (f "a") (list :lex (list 3))) 'type-error) "an entry that is not a cons")
  (ok (signals (minimize (f "a") (list :lex (list (cons -1 "a")))) 'type-error) "a negative weight"))
