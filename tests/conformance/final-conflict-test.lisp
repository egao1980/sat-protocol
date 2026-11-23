(in-package #:sat-protocol/conformance)

;;; 0.2 BACKEND-FINAL-CONFLICT: a cheap core (not necessarily minimal), and
;;; UNSAT-CORE :MINIMAL NIL, which maps it back to the given objects.

(defun subsequence-p (sub list &key (test #'eql))
  "SUB is LIST with some elements left out (order kept, compared with TEST)."
  (loop for x in list
        when (and sub (funcall test x (first sub))) do (pop sub))
  (null sub))

(deftest final-conflict-random
  (let ((rng (make-rng 131)) (unsat-count 0) (sat-count 0))
    (dotimes (i 40)
      (let* ((clauses (random-3sat rng 6 10))
             (assumptions (remove-duplicates
                           (loop repeat 6 collect (let ((v (1+ (rng-int rng 6))))
                                                    (if (zerop (rng-int rng 2)) v (- v))))
                           :from-end t))
             (unsat (not (brute-satisfiable-p (append clauses (mapcar #'list assumptions)) 6))))
        (multiple-value-bind (core status literals)
            (backend-final-conflict *sat-backend* (clauses->cnf clauses 6) assumptions)
          (ok (eq unsat status) (format nil "instance ~D status" i))
          (if unsat
              (progn
                (incf unsat-count)
                (ok (subsequence-p core assumptions) "a sublist of the assumptions, in order")
                (ok (not (brute-satisfiable-p (append clauses (mapcar #'list core)) 6))
                    "the core is unsatisfiable with the CNF"))
              (progn
                (incf sat-count)
                (ok (null core))
                (ok (subsetp assumptions literals) "the answer assigns the assumptions")
                (ok (every (lambda (c) (some (lambda (l) (member l literals)) c)) clauses)
                    "the answer satisfies every clause (as BACKEND-SOLVE's)"))))))
    (ok (and (plusp unsat-count) (plusp sat-count)) "both outcomes exercised")))

(deftest final-conflict-leaves-cnf-alone
  (let* ((cnf (clauses->cnf '((1 2) (-1 2)) 2))
         (before (cnf-clauses cnf)))
    (backend-final-conflict *sat-backend* cnf '(-2))
    (ok (equal before (cnf-clauses cnf)))
    (ok (= 2 (cnf-variable-count cnf)))))

(deftest final-conflict-budget
  (multiple-value-bind (clauses n) (pigeonhole 4 3)
    (let ((cnf (clauses->cnf clauses n)))
      (ok (signals (backend-final-conflict *sat-backend* cnf '() :budget 1) 'sat-budget-exceeded))
      (ok (eq t (nth-value 1 (backend-final-conflict *sat-backend* cnf '() :budget nil)))))))

(deftest unsat-core-not-minimal
  (let* ((a (sat-var "a")) (not-c (sat-not (sat-var "c"))) (d (sat-var "d")))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:and (:implies "a" "b") (:implies "b" "c")))
                    :assumptions (list d a not-c) :minimal nil)
      (ok (eq t unsat))
      (ok (subsequence-p core (list d a not-c)) "the given objects, given order")
      (ok (and (member a core) (member not-c core)) "both members of the only core")))
  (ok (equal '(nil nil)
             (multiple-value-list
              (unsat-core (f '(:or "a" "b")) :assumptions '("a" "b") :minimal nil))))
  (multiple-value-bind (core unsat)
      (unsat-core (sat-true)
                  :named (list (cons "root" (f "app"))
                               (cons "other" (f "c"))
                               (cons "dep" (f '(:implies "app" "lib")))
                               (cons "pin" (f '(:not "lib"))))
                  :minimal nil)
    (ok (eq t unsat))
    (ok (subsequence-p core '("root" "other" "dep" "pin") :test #'equal))
    (ok (every (lambda (name) (member name core :test #'equal)) '("root" "dep" "pin")))))

(deftest unsat-core-minimal-default
  ;; :MINIMAL T is the 0.1 behaviour.
  (let ((formula (f '(:and (:implies "a" "b") (:implies "b" "c"))))
        (assumptions (list (sat-var "d") (sat-var "a") (sat-not (sat-var "c")))))
    (ok (equal (multiple-value-list (unsat-core formula :assumptions assumptions))
               (multiple-value-list (unsat-core formula :assumptions assumptions :minimal t))))))
