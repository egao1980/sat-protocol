(in-package #:sat-protocol/tests)

;;; 0.2 MINIMIZE / BACKEND-MINIMIZE / BACKEND-FINAL-CONFLICT wiring, on
;;; REFERENCE-BACKEND (protocol default methods): what the backends receive,
;;; the budget meter, the 0.1 compatibility, the STORE-VALUE restart.

(defclass call-recording-backend (reference-backend)
  ((minimize-calls :initform nil :accessor minimize-calls)
   (solve-calls :initform nil :accessor solve-calls)
   (final-conflict-calls :initform nil :accessor final-conflict-calls))
  (:default-initargs :propagate t)
  (:documentation "The propagating reference search, recording the arguments of
BACKEND-MINIMIZE, BACKEND-SOLVE and BACKEND-FINAL-CONFLICT (newest first)."))

(defmethod backend-minimize :around ((b call-recording-backend) cnf objective
                                     &rest args &key &allow-other-keys)
  (declare (ignore cnf))
  (push (cons objective args) (minimize-calls b))
  (call-next-method))

(defmethod backend-solve :around ((b call-recording-backend) cnf &rest args &key &allow-other-keys)
  (declare (ignore cnf))
  (push args (solve-calls b))
  (call-next-method))

(defmethod backend-final-conflict :around ((b call-recording-backend) cnf assumptions
                                           &rest args &key &allow-other-keys)
  (declare (ignore cnf))
  (push (cons assumptions args) (final-conflict-calls b))
  (call-next-method))

(defun recorder () (make-instance 'call-recording-backend))

(defun sample-chain ()
  "A clause-shaped chain whose worst labelling is not optimal."
  (find-if (lambda (c)
             (let ((worst (chain-worst-labelling c)))
               (and worst (< (first (chain-dp c)) (first (chain-labelling-cost c worst))))))
           (random-chains 77 8 :positions 3)))

;;; ------------------------------------------------------- 0.1 compatibility

(deftest minimize-0.1-calls
  (ok (equal '((("a" . nil) ("b" . t) ("c" . nil)) 1 t)
             (multiple-value-list
              (minimize (f '(:or "a" "b" "c")) (list (cons 3 "a") (cons 1 "b") (cons 2 "c")))))
      "the 0.1 result plus OPTIMAL-P T")
  (ok (equal '(nil nil)
             (multiple-value-list (minimize (f '(:and "a" (:not "a"))) (list (cons 1 "a")))))
      "UNSAT: exactly two values")
  (let ((cnf (clauses->cnf '((1 2)) 2)))
    (multiple-value-bind (literals cost optimal-p)
        (backend-minimize *sat-backend* cnf '((1 . 1) (1 . 2)))
      (ok (eql 1 cost) "a 0.1-style BACKEND-MINIMIZE call")
      (ok (eq t optimal-p))
      (ok (= 1 (count-if #'plusp literals))))))

;;; ------------------------------------------------- what the backend gets

(deftest backend-minimize-receives-index-arguments
  (let ((b (recorder)))
    (minimize (f '(:or "a" "b")) (list (cons 1 "a")) :backend b
              :strategy :stratified :budget 500 :timeout 30
              :hint (list (sat-var "b")) :phase :true :order #'first
              :assumptions (list (sat-not (sat-var "a"))))
    (ok (= 1 (length (minimize-calls b))) "one BACKEND-MINIMIZE call")
    (destructuring-bind (objective &key assumptions strategy budget timeout order phase hint
                         &allow-other-keys)
        (first (minimize-calls b))
      (ok (equal '((1 . 1)) objective))
      (ok (equal '(-1) assumptions))
      (ok (eq :stratified strategy))
      (ok (eql 500 budget))
      (ok (eql 30 timeout))
      (ok (equal '(2) hint) "hint literals as integers")
      (ok (functionp order) "index-level ORDER")
      (ok (functionp phase) "index-level PHASE")))
  (let ((b (recorder)))
    (multiple-value-bind (model cost)
        (minimize (f '(:or "a" "b"))
                  (list :lex (list (cons 1 "a")) (list (cons 2 (sat-not (sat-var "b")))))
                  :backend b)
      (ok (equal '(:lex ((1 . 1)) ((2 . -2))) (car (first (minimize-calls b)))) ":lex at index level")
      (ok (equal '(0 0) cost))
      (ok (equal '(("a" . nil) ("b" . t)) model)))))

(deftest minimize-passes-order-and-phase
  (let ((c (sample-chain)))
    (dolist (strategy *strategies*)
      (let ((b (recorder)))
        (minimize (chain-formula c) (chain-objective c) :backend b :strategy strategy
                                                         :order #'first :phase :false)
        (ok (plusp (length (solve-calls b))))
        (ok (every (lambda (args) (and (functionp (getf args :order)) (functionp (getf args :phase))))
                   (solve-calls b))
            (format nil "~A: every BACKEND-SOLVE call" strategy))
        (ok (every (lambda (call) (and (functionp (getf (cdr call) :order))
                                       (functionp (getf (cdr call) :phase))))
                   (final-conflict-calls b))
            (format nil "~A: every BACKEND-FINAL-CONFLICT call" strategy))))))

(deftest minimize-first-call-assumes-hint
  (dolist (strategy *strategies*)
    (let ((b (recorder)))
      (minimize (f '(:or "a" "b" "c")) (list (cons 1 "a")) :backend b :strategy strategy
                :assumptions (list "a") :hint (list "b" (sat-not (sat-var "c"))))
      (let ((first-call (first (last (solve-calls b)))))
        (ok (equal '(-3 1 2) (sort (copy-list (getf first-call :assumptions)) #'<))
            (format nil "~A: ASSUMPTIONS plus the hint" strategy))))))

(deftest minimize-metered-calls
  (let ((c (sample-chain)))
    (dolist (strategy *strategies*)
      (let ((b (recorder)))
        (minimize (chain-formula c) (chain-objective c) :backend b :strategy strategy
                                                         :budget 100000)
        (ok (every (lambda (args) (integerp (getf args :budget))) (solve-calls b))
            (format nil "~A: every BACKEND-SOLVE call runs with an integer :BUDGET" strategy))))))

(deftest minimize-hides-backend-budget-signals
  (let ((c (sample-chain)))
    (dolist (strategy *strategies*)
      (let ((seen 0)
            (hint (chain-model c (chain-worst-labelling c))))
        (handler-bind ((sat-budget-exceeded (lambda (e) (declare (ignore e)) (incf seen))))
          (minimize (chain-formula c) (chain-objective c) :strategy strategy :budget 0 :hint hint))
        (ok (zerop seen) (format nil "~A: an incumbent, so no signal reaches the caller" strategy)))
      (let ((seen 0))
        (ok (eq :none (handler-bind ((sat-budget-exceeded (lambda (e) (incf seen) (use-value :none e))))
                        (minimize (chain-formula c) (chain-objective c) :strategy strategy :budget 0))))
        (ok (= 1 seen) (format nil "~A: one signal, MINIMIZE's own" strategy))))))

(deftest core-guided-uses-final-conflict
  (let ((b (recorder)))
    (multiple-value-bind (model cost optimal-p)
        (minimize (f '(:or "a" "b")) (list (cons 1 "a") (cons 1 "b")) :backend b :strategy :core-guided)
      (ok model)
      (ok (eql 1 cost))
      (ok (eq t optimal-p)))
    (ok (plusp (length (final-conflict-calls b))))
    (ok (every (lambda (call) (every #'integerp (car call))) (final-conflict-calls b)))))

(deftest minimize-leaves-cnf-alone
  (dolist (strategy *strategies*)
    (let* ((cnf (clauses->cnf '((1 2 3) (-1 -2)) 3))
           (before (cnf-clauses cnf)))
      (minimize cnf (list (cons 1 1) (cons 2 2) (cons 3 3)) :strategy strategy
                                                             :hint (list (sat-var 3)) :budget 1000)
      (ok (equal before (cnf-clauses cnf)) (format nil "~A: clauses" strategy))
      (ok (= 3 (cnf-variable-count cnf)) (format nil "~A: variables" strategy)))))

(deftest minimize-no-backend-0.2
  (let ((*sat-backend* nil))
    (ok (signals (minimize (f "a") nil :strategy :core-guided) 'sat-no-backend))
    (ok (equal '(:none nil)
               (handler-bind ((sat-no-backend (lambda (c) (use-value :none c))))
                 (multiple-value-list (minimize (f "a") nil :budget 10)))))))

;;; ------------------------------------------------ BACKEND-FINAL-CONFLICT

(deftest final-conflict-default-method
  (let ((b (make-instance 'reference-backend))
        (cnf (clauses->cnf '((1 2)) 2))
        (assumptions (list -1 -1 -2)))
    (multiple-value-bind (core unsat) (backend-final-conflict b cnf assumptions)
      (ok (eq t unsat))
      (ok (equal '(-1 -1 -2) core) "all of the assumptions, as given")
      (ok (not (eq assumptions core)) "a fresh list"))
    (multiple-value-bind (core unsat literals) (backend-final-conflict b cnf '(-1))
      (ok (null core))
      (ok (null unsat))
      (ok (and (member -1 literals) (member 2 literals)) "the answer of the BACKEND-SOLVE call"))))

(deftest unsat-core-minimal-nil-calls-final-conflict
  (let ((b (recorder)))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:not "a")) :assumptions (list "a" "b") :backend b :minimal nil)
      (ok (eq t unsat))
      (ok (member "a" core :test #'equal)))
    (ok (= 1 (length (final-conflict-calls b))))))

;;; ------------------------------------------------------ STORE-VALUE (0.2)

(deftest signal-budget-exceeded-store-value
  (ok (eql 7 (handler-bind ((sat-budget-exceeded (lambda (c) (store-value 7 c))))
               (signal-budget-exceeded 3)))
      "STORE-VALUE sets the budget")
  (ok (signals (handler-bind ((sat-budget-exceeded (lambda (c) (store-value -1 c))))
                 (signal-budget-exceeded 3))
               'type-error)
      "a negative budget is a TYPE-ERROR")
  (let ((budgets '()))
    (multiple-value-bind (clauses n) (pigeonhole 4 3)
      (ok (equal '(nil nil)
                 (handler-bind ((sat-budget-exceeded
                                  (lambda (c)
                                    (push (sat-budget-exceeded-budget c) budgets)
                                    (store-value (1+ (sat-budget-exceeded-budget c)) c))))
                   (multiple-value-list (solve (clauses->cnf clauses n) :budget 0))))
          "stepping the budget one decision at a time finishes the search"))
    (ok (plusp (length budgets)))
    (ok (equal (reverse budgets) (loop for i below (length budgets) collect i))
        "signalled before every decision: 0, 1, 2, ...")))

(deftest budget-exceeded-timeout-slot
  (let ((c (make-condition 'sat-budget-exceeded :timeout 5)))
    (ok (eql 5 (sat-budget-exceeded-timeout c)))
    (ok (null (sat-budget-exceeded-budget c)))
    (ok (search "5 second" (princ-to-string c))))
  (ok (null (sat-budget-exceeded-timeout (make-condition 'sat-budget-exceeded :budget 3)))))
