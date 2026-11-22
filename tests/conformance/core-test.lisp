(in-package #:sat-protocol/conformance)

;;; unsat-core: subsets of the assumptions / named formulas, unsatisfiable, minimal.

(deftest core-chain
  (let* ((a (sat-var "a")) (not-c (sat-not (sat-var "c"))) (d (sat-var "d")))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:and (:implies "a" "b") (:implies "b" "c")))
                    :assumptions (list d a not-c))
      (ok (eq t unsat))
      (ok (= 2 (length core)))
      (ok (and (eq a (first core)) (eq not-c (second core))) "the given objects, given order"))))

(deftest core-satisfiable
  (ok (equal '(nil nil)
             (multiple-value-list (unsat-core (f '(:or "a" "b")) :assumptions '("a" "b"))))))

(deftest core-hard-part-unsat
  (ok (equal '(nil t)
             (multiple-value-list (unsat-core (f '(:and "a" (:not "a"))) :assumptions '("b"))))))

(deftest core-named
  (multiple-value-bind (core unsat)
      (unsat-core (sat-true)
                  :named (list (cons "root" (f "app"))
                               (cons "other" (f "c"))
                               (cons "dep" (f '(:implies "app" "lib")))
                               (cons "pin" (f '(:not "lib")))))
    (ok (eq t unsat))
    (ok (equal '("root" "dep" "pin") core))))

(deftest core-mixed
  (let ((x (sat-var "x")))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:implies "x" "y"))
                    :assumptions (list x)
                    :named (list (cons :no-y (f '(:not "y"))) (cons :z (f "z"))))
      (ok (eq t unsat))
      (ok (equal (list x :no-y) core) "assumptions first, then names"))))

(defun %lit-formula (lit)
  (if (plusp lit) (sat-var lit) (sat-not (sat-var (- lit)))))

(deftest core-random-minimality
  (let ((rng (make-rng 99)) (checked 0))
    (dotimes (i 40)
      (let* ((clauses (random-3sat rng 6 10))
             (lits (remove-duplicates
                    (loop repeat 6 collect (let ((v (1+ (rng-int rng 6))))
                                             (if (zerop (rng-int rng 2)) v (- v))))))
             (assumptions (mapcar #'%lit-formula lits)))
        (flet ((unsat-with (subset)
                 (not (brute-satisfiable-p
                       (append clauses
                               (mapcar (lambda (a) (list (nth (position a assumptions) lits)))
                                       subset))
                       6))))
          (multiple-value-bind (core unsat)
              (unsat-core (clauses->cnf clauses 6) :assumptions assumptions)
            (ok (eq (unsat-with assumptions) unsat) (format nil "instance ~D status" i))
            (when (and unsat (not (unsat-with nil)))
              (incf checked)
              (ok (every (lambda (c) (member c assumptions :test #'eq)) core) "drawn from the assumptions")
              (ok (unsat-with core) "the core is unsatisfiable")
              (ok (every (lambda (c) (not (unsat-with (remove c core :test #'eq)))) core)
                  "minimal: dropping any element is satisfiable"))))))
    (ok (plusp checked) "some instances have a non-empty core")))
