(in-package #:sat-protocol/tests)

;;; Front ends <-> backends: dispatch, arguments, SAT-NO-BACKEND, budgets.

(defclass recording-backend (reference-backend)
  ((calls :initform nil :accessor recording-calls))
  (:documentation "The reference search, recording each BACKEND-SOLVE call's arguments."))

(defmethod backend-solve ((b recording-backend) cnf &rest args &key &allow-other-keys)
  (push (cons cnf args) (recording-calls b))
  (call-next-method))

(deftest nickname
  (ok (eq (find-package '#:sat-protocol) (find-package '#:stack-sat))))

(deftest model-value-lookup
  (let ((model '(("a" . t) ("b" . nil))))
    (ok (equal '(t t) (multiple-value-list (model-value model "a"))))
    (ok (equal '(nil t) (multiple-value-list (model-value model "b"))))
    (ok (equal '(nil nil) (multiple-value-list (model-value model "c"))))))

(deftest no-backend-signals
  (let ((*sat-backend* nil))
    (ok (signals (solve (f "a")) 'sat-no-backend))
    (ok (signals (solve-all (f "a")) 'sat-no-backend))
    (ok (signals (minimize (f "a") nil) 'sat-no-backend))
    (ok (signals (unsat-core (f "a")) 'sat-error))
    (let ((formula (f "a")))
      (ok (eq formula (handler-case (solve formula)
                        (sat-no-backend (c) (sat-no-backend-formula c))))))
    (ok (search "backend" (string-downcase
                           (handler-case (solve (f "a"))
                             (sat-no-backend (c) (princ-to-string c))))))))

(deftest no-backend-use-backend
  (let ((*sat-backend* nil))
    (ok (equal '((("a" . t)) t)
               (handler-bind ((sat-no-backend
                                (lambda (c) (use-backend (make-instance 'reference-backend) c))))
                 (multiple-value-list (solve (f "a"))))))
    (ok (= 1 (length (handler-bind ((sat-no-backend
                                      (lambda (c) (use-backend (make-instance 'reference-backend) c))))
                       (collect-models (solve-all (f '(:and "a" "b"))))))))))

(deftest no-backend-use-value
  (let ((*sat-backend* nil))
    (ok (equal '(:none nil)
               (handler-bind ((sat-no-backend (lambda (c) (use-value :none c))))
                 (multiple-value-list (solve (f "a"))))))
    (ok (equal '(:none nil)
               (handler-bind ((sat-no-backend (lambda (c) (use-value :none c))))
                 (multiple-value-list (minimize (f "a") nil)))))))

(deftest backend-argument-overrides-special
  (let ((b (make-instance 'recording-backend))
        (*sat-backend* (make-instance 'recording-backend)))
    (solve (f "a") :backend b)
    (ok (= 1 (length (recording-calls b))))
    (ok (null (recording-calls *sat-backend*)))))

(deftest backend-receives-integer-arguments
  (let ((b (make-instance 'recording-backend)))
    (solve (f '(:or "a" "b")) :backend b :assumptions (list (sat-not (sat-var "b"))) :budget 5)
    (destructuring-bind (cnf &key assumptions order phase budget) (first (recording-calls b))
      (ok (cnf-p cnf))
      (ok (equal '(-2) assumptions))
      (ok (null order) "no :order -> NIL")
      (ok (null phase) "no :phase -> NIL")
      (ok (eql 5 budget)))
    (setf (recording-calls b) nil)
    (solve (f '(:or "a" "b")) :backend b :phase :true
           :order (lambda (names) (first names)))
    (destructuring-bind (cnf &key order phase &allow-other-keys) (first (recording-calls b))
      (declare (ignore cnf))
      (ok (functionp order))
      (ok (functionp phase))
      (ok (eql 2 (funcall order '(2))) "index-level order: names mapped back to indices")
      (ok (eq t (funcall phase 1))))))

(deftest default-methods-use-backend-solve
  ;; RECORDING-BACKEND implements only BACKEND-SOLVE: the protocol's default
  ;; methods do the rest.
  (let ((b (make-instance 'recording-backend)))
    (ok (= 3 (length (collect-models (solve-all (f '(:or "a" "b")) :backend b)))))
    (ok (plusp (length (recording-calls b))))
    (ok (eql 0 (nth-value 1 (minimize (f '(:or "a" "b")) (list (cons 1 "a")) :backend b))))
    (ok (equal '("a") (unsat-core (f '(:not "a")) :assumptions '("a") :backend b)))))

(deftest signal-budget-exceeded-restarts
  (ok (signals (signal-budget-exceeded 3) 'sat-budget-exceeded))
  (ok (eql 6 (handler-bind ((sat-budget-exceeded #'continue))
               (signal-budget-exceeded 3)))
      "CONTINUE doubles")
  (ok (eql 2 (handler-bind ((sat-budget-exceeded #'continue))
               (signal-budget-exceeded 0)))
      "at least 1, doubled")
  (ok (search "3" (handler-case (signal-budget-exceeded 3)
                    (sat-budget-exceeded (c) (princ-to-string c))))))
