;;;; Conditions and restarts (CLHS 9). GIVEN.
;;;;
;;;; SAT-INVALID-FORMULA    A constructor operand that is not a formula, a SAT-VAR
;;;;                        name of NIL, or a bad sexp in SEXP->FORMULA. Signalled
;;;;                        inside RESTART-CASE with USE-VALUE (value): use VALUE
;;;;                        instead (a formula, or for SAT-VAR a name; it is
;;;;                        checked again).
;;;; SAT-UNBOUND-VARIABLE   FORMULA-EVAL met a variable the assignment does not
;;;;                        bind (and no :DEFAULT was given). USE-VALUE (boolean):
;;;;                        use it for this occurrence.
;;;; SAT-NO-BACKEND         A front end (SOLVE, SOLVE-ALL, MINIMIZE, UNSAT-CORE)
;;;;                        found neither :BACKEND nor *SAT-BACKEND*. USE-BACKEND
;;;;                        (backend): retry with it. USE-VALUE (value): the front
;;;;                        end returns (values VALUE NIL).
;;;; SAT-BUDGET-EXCEEDED    A backend made more decisions than :BUDGET. Signalled by
;;;;                        SIGNAL-BUDGET-EXCEEDED (backends call it). CONTINUE:
;;;;                        double the budget and keep searching. STORE-VALUE
;;;;                        (budget), 0.2: keep searching with that budget (a
;;;;                        non-negative integer: the most decisions of the whole
;;;;                        call; the backend signals again before the decision that
;;;;                        would exceed it). USE-VALUE (value): the front end
;;;;                        returns (values VALUE NIL).
;;;;                        0.2: MINIMIZE also signals it when its :BUDGET or
;;;;                        :TIMEOUT runs out before any model was found (see
;;;;                        minimize.lisp). Then exactly one of BUDGET (decisions)
;;;;                        and TIMEOUT (seconds) is non-NIL: the limit that ran out.
;;;;                        CONTINUE doubles that limit (a budget as
;;;;                        SIGNAL-BUDGET-EXCEEDED does; a timeout T becomes
;;;;                        (max (* 2 T) 1)); USE-VALUE: MINIMIZE returns
;;;;                        (values VALUE NIL).
;;;; SAT-DIMACS-ERROR       READ-DIMACS met a malformed line. SKIP-LINE: ignore the
;;;;                        line. CONTINUE (header count mismatches only): accept
;;;;                        the actual counts.
;;;;
;;;; 0.3 (L2b-2, sessions: the rules are in session.lisp):
;;;; SAT-SESSION-CLOSED     A session operation on a closed session (every
;;;;                        operation but CLOSE-SESSION, SESSION-OPEN-P,
;;;;                        SESSION-BACKEND and SESSION-BACKEND-STATE). Signalled
;;;;                        before the operation does anything, inside
;;;;                        RESTART-CASE with USE-VALUE (value): the operation
;;;;                        returns VALUE (SESSION-SOLVE, SESSION-MINIMIZE,
;;;;                        SESSION-MODEL and SESSION-UNSAT-CORE return (values
;;;;                        VALUE NIL)).
;;;; SAT-BUDGET-REACHED     NOT an error (a CONDITION signalled with SIGNAL).
;;;;                        SESSION-MINIMIZE spent its :BUDGET with an incumbent.
;;;;                        BUDGET: that budget; COST: the incumbent's cost (a
;;;;                        list for :lex). Restarts: USE-BEST: stop and return the
;;;;                        incumbent; CONTINUE: double the budget (2 x (max BUDGET
;;;;                        1)) and resume; STORE-VALUE (budget): resume with that
;;;;                        budget (a non-negative integer, the most decisions of
;;;;                        the whole call). Unhandled (SIGNAL returns), the call
;;;;                        takes USE-BEST, so a call without a handler returns
;;;;                        what MINIMIZE would: the incumbent, OPTIMAL-P NIL.

(in-package #:sat-protocol)

(define-condition sat-error (error)
  ((message :initarg :message :reader sat-error-message :initform nil))
  (:report (lambda (c s)
             (format s "SAT error~@[: ~A~]" (sat-error-message c))))
  (:documentation "Root of every sat-protocol condition."))

(define-condition sat-invalid-formula (sat-error)
  ((datum :initarg :datum :reader sat-invalid-formula-datum :initform nil))
  (:report (lambda (c s)
             (format s "Invalid SAT formula~@[ (~A)~]: ~S"
                     (sat-error-message c) (sat-invalid-formula-datum c))))
  (:documentation "DATUM is not a formula (or not a valid variable name / sexp)."))

(define-condition sat-unbound-variable (sat-error)
  ((name :initarg :name :reader sat-unbound-variable-name))
  (:report (lambda (c s)
             (format s "SAT variable ~S has no value in the assignment"
                     (sat-unbound-variable-name c))))
  (:documentation "FORMULA-EVAL found a variable the assignment does not bind."))

(define-condition sat-no-backend (sat-error)
  ((formula :initarg :formula :reader sat-no-backend-formula :initform nil))
  (:report (lambda (c s)
             (declare (ignore c))
             (format s "No SAT backend; bind ~S or pass :backend (e.g. load sat-backend-dpll)"
                     '*sat-backend*)))
  (:documentation "A front end found no backend for FORMULA."))

(define-condition sat-budget-exceeded (sat-error)
  ((budget :initarg :budget :reader sat-budget-exceeded-budget :initform nil)
   (timeout :initarg :timeout :reader sat-budget-exceeded-timeout :initform nil
            :documentation "0.2: MINIMIZE's :TIMEOUT (seconds) when that is what ran out."))
  (:report (lambda (c s)
             (if (sat-budget-exceeded-timeout c)
                 (format s "SAT search exceeded its timeout of ~A second~:P"
                         (sat-budget-exceeded-timeout c))
                 (format s "SAT search exceeded its budget of ~D decision~:P"
                         (sat-budget-exceeded-budget c)))))
  (:documentation "A backend made more decisions than the :BUDGET of the call, or
(0.2) MINIMIZE ran out of :BUDGET or :TIMEOUT before finding any model."))

(define-condition sat-dimacs-error (sat-error)
  ((line :initarg :line :reader sat-dimacs-error-line :initform nil)
   (line-number :initarg :line-number :reader sat-dimacs-error-line-number :initform nil))
  (:report (lambda (c s)
             (format s "DIMACS error~@[ at line ~D~]~@[: ~A~]~@[ in ~S~]"
                     (sat-dimacs-error-line-number c)
                     (sat-error-message c)
                     (sat-dimacs-error-line c))))
  (:documentation "Malformed DIMACS input. LINE is the offending text (1-based LINE-NUMBER)."))

(define-condition sat-session-closed (sat-error)
  ((session :initarg :session :reader sat-session-closed-session :initform nil))
  (:report (lambda (c s)
             (format s "SAT session ~A is closed" (sat-session-closed-session c))))
  (:documentation "0.3: an operation on a closed SAT-SESSION."))

(define-condition sat-budget-reached (condition)
  ((budget :initarg :budget :reader sat-budget-reached-budget :initform nil)
   (cost :initarg :cost :reader sat-budget-reached-cost :initform nil))
  (:report (lambda (c s)
             (format s "SAT search reached its budget of ~D decision~:P with an incumbent of cost ~S"
                     (sat-budget-reached-budget c) (sat-budget-reached-cost c))))
  (:documentation "0.3: SESSION-MINIMIZE spent its budget and has an incumbent.
Not an error: signalled with SIGNAL; unhandled, the call returns the incumbent."))

;;; Restart helpers. CL's USE-VALUE and CONTINUE cover the others.

(defun use-backend (backend &optional condition)
  "Invoke the USE-BACKEND restart of SAT-NO-BACKEND (retry with BACKEND)."
  (let ((restart (find-restart 'use-backend condition)))
    (if restart
        (invoke-restart restart backend)
        (error 'control-error))))

(defun use-best (&optional condition)
  "0.3: invoke the USE-BEST restart of SAT-BUDGET-REACHED (return the incumbent)."
  (let ((restart (find-restart 'use-best condition)))
    (if restart
        (invoke-restart restart)
        (error 'control-error))))

(defun skip-line (&optional condition)
  "Invoke the SKIP-LINE restart of SAT-DIMACS-ERROR (ignore the line)."
  (let ((restart (find-restart 'skip-line condition)))
    (if restart
        (invoke-restart restart)
        (error 'control-error))))

;;; Front-end exits. Every front end (SOLVE, SOLVE-ALL's NEXT-MODEL, MINIMIZE,
;;; UNSAT-CORE) runs its body inside (CATCH '%SAT-FRONT-VALUE ...), so the
;;; USE-VALUE restarts below make that call return (values VALUE NIL).

(defun %front-value (value)
  (throw '%sat-front-value (values value nil)))

(defun %read-budget ()
  (format *query-io* "New budget (decisions): ")
  (force-output *query-io*)
  (list (read *query-io*)))

(defun signal-budget-exceeded (budget)
  "For backends: call when the search has made more than BUDGET decisions.
Signals SAT-BUDGET-EXCEEDED. Returns the new budget (2 x BUDGET, at least 1)
when the handler invokes CONTINUE, or the value given to STORE-VALUE (0.2: a
non-negative integer, the new budget of the whole call); USE-VALUE makes the
front end return."
  (restart-case (error 'sat-budget-exceeded :budget budget)
    (continue ()
      :report "Double the budget and keep searching."
      (* 2 (max budget 1)))
    (store-value (new-budget)
      :report "Keep searching with another budget."
      :interactive %read-budget
      (check-type new-budget (integer 0 *))
      new-budget)
    (use-value (value)
      :report "Stop searching; the call returns VALUE."
      (%front-value value))))

(defun %resolve-backend (backend formula)
  "BACKEND, else *SAT-BACKEND*, else signal SAT-NO-BACKEND with USE-BACKEND
(retry with that backend) and USE-VALUE (the front end returns the value)."
  (loop
    (let ((b (or backend (symbol-value '*sat-backend*))))
      (when b (return b))
      (restart-case (error 'sat-no-backend :formula formula)
        (use-backend (new)
          :report "Retry with another backend."
          (setf backend new))
        (use-value (value)
          :report "Return a value instead."
          (%front-value value))))))
