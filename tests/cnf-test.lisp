(in-package #:sat-protocol/tests)

;;; CNF object, variable table, clause-shaped conversion, Tseitin.

(deftest empty-cnf
  (let ((cnf (make-cnf)))
    (ok (cnf-p cnf))
    (ok (= 0 (cnf-variable-count cnf)))
    (ok (= 0 (cnf-clause-count cnf)))
    (ok (null (cnf-clauses cnf)))
    (ok (null (cnf-user-variables cnf)))))

(deftest variable-table
  (let ((cnf (make-cnf)))
    (ok (= 1 (cnf-ensure-variable cnf "a")))
    (ok (= 2 (cnf-ensure-variable cnf '(pkg 2))))
    (ok (= 1 (cnf-ensure-variable cnf "a")) "existing name, same index")
    (ok (= 3 (cnf-ensure-variable cnf nil)) "NIL allocates an auxiliary")
    (ok (= 4 (cnf-ensure-variable cnf nil)) "a fresh one each time")
    (ok (= 4 (cnf-variable-count cnf)))
    (ok (equal '(pkg 2) (cnf-variable-name cnf 2)))
    (ok (null (cnf-variable-name cnf 3)))
    (ok (cnf-aux-variable-p cnf 3))
    (ok (not (cnf-aux-variable-p cnf 1)))
    (ok (eql 2 (cnf-variable-index cnf (list 'pkg 2))) "EQUAL names")
    (ok (null (cnf-variable-index cnf "nope")))
    (ok (equal '("a" (pkg 2)) (cnf-user-variables cnf)))))

(deftest literals-to-integers
  (let ((cnf (make-cnf)))
    (ok (= -1 (cnf-literal cnf (sat-not (sat-var "a")))))
    (ok (= 2 (cnf-literal cnf "b")) "bare name allocates")
    (ok (= 1 (cnf-literal cnf (sat-var "a"))))
    (ok (signals (cnf-literal cnf (sat-and (sat-var "a") (sat-var "b"))) 'sat-invalid-formula))))

(deftest add-clauses
  (let ((cnf (make-cnf)))
    (cnf-ensure-variable cnf "a")
    (cnf-ensure-variable cnf "b")
    (ok (eq cnf (cnf-add-clause cnf '(1 -2))))
    (cnf-add-clause cnf '(2))
    (cnf-add-clause cnf '())
    (ok (equal '((1 -2) (2) ()) (cnf-clauses cnf)))
    (ok (= 3 (cnf-clause-count cnf)))
    (ok (signals (cnf-add-clause cnf '(1 0)) 'sat-invalid-formula))
    (ok (signals (cnf-add-clause cnf '(3)) 'sat-invalid-formula) "beyond the variable count")
    (ok (signals (cnf-add-clause cnf '("a")) 'sat-invalid-formula))
    (ok (eql 3 (handler-case (cnf-add-clause cnf '(1 3))
                 (sat-invalid-formula (c) (sat-invalid-formula-datum c)))))
    (ok (= 3 (cnf-clause-count cnf)) "a rejected clause adds nothing")))

(deftest clauses-are-fresh
  (let ((cnf (clauses->cnf '((1 2)) 2)))
    (setf (first (first (cnf-clauses cnf))) 99)
    (ok (equal '((1 2)) (cnf-clauses cnf)))))

(deftest copy-is-independent
  (let* ((cnf (clauses->cnf '((1 2)) 2))
         (copy (copy-cnf cnf)))
    (cnf-ensure-variable copy "x")
    (cnf-add-clause copy '(3))
    (ok (= 2 (cnf-variable-count cnf)))
    (ok (equal '((1 2)) (cnf-clauses cnf)))
    (ok (equal '((1 2) (3)) (cnf-clauses copy)))
    (ok (equal '(1 2 "x") (cnf-user-variables copy)))))

(deftest clause-shaped-conversion
  (let ((cnf (to-cnf (f '(:and "a"
                          (:or "b" (:not "c"))
                          (:not (:and "a" "b"))
                          (:implies "a" (:or "b" "c"))
                          (:implies "c" "a")
                          (:implies (:not "a") "b")
                          (:not "c"))))))
    (ok (= 3 (cnf-variable-count cnf)) "no auxiliaries")
    (ok (equal '("a" "b" "c") (cnf-user-variables cnf)))
    (ok (equal '((1) (2 -3) (-1 -2) (-1 2 3) (-3 1) (1 2) (-3)) (cnf-clauses cnf)))))

(deftest constant-conversion
  (ok (null (cnf-clauses (to-cnf (sat-true)))))
  (ok (equal '(()) (cnf-clauses (to-cnf (sat-false)))))
  (ok (equal '((1 2)) (cnf-clauses (to-cnf (f '(:or "a" "b"))))) "a single clause"))

(deftest to-cnf-into-existing
  (let ((cnf (make-cnf)))
    (cnf-ensure-variable cnf "z")
    (ok (eq cnf (to-cnf (f '(:or "a" "z")) :cnf cnf)))
    (ok (equal '((2 1)) (cnf-clauses cnf)))
    (ok (equal '("z" "a") (cnf-user-variables cnf)))))

(deftest to-cnf-of-cnf
  (let ((cnf (clauses->cnf '((1)) 1)))
    (ok (eq cnf (to-cnf cnf)))))

(defun %operator-nodes (sexp)
  (if (or (atom sexp) (eq (first sexp) :var))
      0
      (1+ (reduce #'+ (mapcar #'%operator-nodes (rest sexp))))))

(deftest tseitin-projection
  ;; Models of the CNF projected on the user variables = models of the formula.
  (let ((rng (make-rng 23)) (names '("a" "b" "c" "d")))
    (dotimes (i 40)
      (let* ((formula (f (random-sexp rng names 3)))
             (sexp (formula->sexp formula))
             (cnf (to-cnf formula))
             (user (cnf-user-variables cnf))
             (clauses (cnf-clauses cnf)))
        (ok (equal (formula-variables formula) user) (format nil "formula ~D user variables first" i))
        (ok (equal user (loop for k from 1 to (length user) collect (cnf-variable-name cnf k))))
        (ok (<= (- (cnf-variable-count cnf) (length user)) (%operator-nodes sexp))
            (format nil "formula ~D auxiliaries bounded" i))
        (ok (every (lambda (env)
                     (eq (and (sexp-eval sexp env) t)
                         (nth-value 1 (sat-protocol/conformance:reference-search
                                       clauses
                                       :assumptions (loop for k from 1 for name in user
                                                          collect (if (cdr (assoc name env :test #'equal)) k (- k)))))))
                   (all-assignments user))
            (format nil "formula ~D projection" i))))))
