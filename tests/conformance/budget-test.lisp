(in-package #:sat-protocol/conformance)

;;; :budget (decisions) and the SAT-BUDGET-EXCEEDED restarts. PHP(4,3) needs
;;; more than one decision on any backend without preprocessing.

(defun php-4-3 ()
  (multiple-value-bind (clauses n) (pigeonhole 4 3)
    (clauses->cnf clauses n)))

(deftest budget-exceeded-signals
  (ok (signals (solve (php-4-3) :budget 1) 'sat-budget-exceeded))
  (ok (signals (solve (php-4-3) :budget 1) 'sat-error))
  (ok (eql 1 (handler-case (solve (php-4-3) :budget 1)
               (sat-budget-exceeded (c) (sat-budget-exceeded-budget c))))))

(deftest budget-use-value
  (ok (equal '(:gave-up nil)
             (handler-bind ((sat-budget-exceeded (lambda (c) (use-value :gave-up c))))
               (multiple-value-list (solve (php-4-3) :budget 1))))))

(deftest budget-continue
  (let ((signals 0))
    (ok (equal '(nil nil)
               (handler-bind ((sat-budget-exceeded (lambda (c) (incf signals) (continue c))))
                 (multiple-value-list (solve (php-4-3) :budget 1))))
        "CONTINUE doubles the budget until the search finishes")
    (ok (plusp signals))))

(deftest budget-nil-unlimited
  (ok (equal '(nil nil)
             (handler-bind ((sat-budget-exceeded (lambda (c) (declare (ignore c)) (error "signalled"))))
               (multiple-value-list (solve (php-4-3)))))))

(deftest budget-large-enough
  (multiple-value-bind (model sat) (solve (f '(:or "a" "b")) :budget 100)
    (ok sat)
    (ok (sexp-eval '(:or "a" "b") model))))
