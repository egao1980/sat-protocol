;;;; REFERENCE-BACKEND: cl-repository's naive search (src/client/solver.lisp
;;;; SAT-SOLVE) over CNF, as a test oracle. No unit propagation, no learning:
;;;; at each node, a falsified clause fails; no clause without a true literal
;;;; succeeds; otherwise decide a candidate (ORDER, else the lowest index), try
;;;; PHASE's value (else T) first, then the other. Only for small instances.
;;;; GIVEN test code.
;;;;
;;;; 0.2: (make-instance 'reference-backend :propagate t) adds unit propagation
;;;; before each decision (the 0.1 default is unchanged). sat-protocol/tests runs
;;;; the whole suite with it: the optimisation tests (strategies, chains, :lex)
;;;; are exponential on the naive search. The naive search is still what
;;;; RECORDING-BACKEND (backend-test) and the order-hook comparison describe.

(in-package #:sat-protocol/conformance)

(defun reference-search (clauses &key assumptions order phase budget propagate)
  "Search integer CLAUSES. Returns (values literals T) or (values NIL NIL).
PROPAGATE (0.2): before each decision, assign the literal of the first unit
clause (no true literal, one unassigned) and repeat; such literals are not
decisions and are undone with the decision they follow."
  (let ((assignment (make-hash-table))
        (decisions 0))
    (labels ((lit-value (lit)
               (multiple-value-bind (v bound) (gethash (abs lit) assignment)
                 (if bound (if (plusp lit) v (not v)) :free)))
             (candidates ()
               ;; :CONFLICT, or (values CANDIDATES UNIT): the ascending candidate
               ;; list (NIL = all satisfied) and the first unit literal or NIL.
               (let ((cands nil) (unit nil))
                 (dolist (c clauses (values (sort (remove-duplicates cands) #'<) unit))
                   (let ((satisfied nil) (free nil))
                     (dolist (l c)
                       (let ((v (lit-value l)))
                         (cond ((eq v :free) (push l free))
                               (v (setf satisfied t)))))
                     (unless satisfied
                       (cond ((null free) (return :conflict))
                             (t (when (and (null unit) (null (rest free)))
                                  (setf unit (first free)))
                                (setf cands (nconc (mapcar #'abs free) cands)))))))))
             (undo (vars)
               (dolist (v vars) (remhash v assignment)))
             (search-node (implied)
               ;; IMPLIED: variables propagated since the last decision.
               (multiple-value-bind (cands unit) (candidates)
                 (cond ((eq cands :conflict) (undo implied) nil)
                       ((null cands) t)
                       ((and propagate unit)
                        (setf (gethash (abs unit) assignment) (plusp unit))
                        (search-node (cons (abs unit) implied)))
                       (t
                        (when (and budget (>= decisions budget))
                          (setf budget (signal-budget-exceeded budget)))
                        (incf decisions)
                        (let* ((var (if order (funcall order cands) (first cands)))
                               (first-value (if phase (and (funcall phase var) t) t)))
                          (dolist (value (list first-value (not first-value))
                                         (progn (remhash var assignment) (undo implied) nil))
                            (setf (gethash var assignment) value)
                            (when (search-node nil) (return t)))))))))
      (dolist (a assumptions)
        (let ((v (lit-value a)))
          (cond ((eq v :free) (setf (gethash (abs a) assignment) (plusp a)))
                ((not v) (return-from reference-search (values nil nil))))))
      (if (search-node nil)
          (values (loop for var being the hash-keys of assignment using (hash-value value)
                        collect (if value var (- var)))
                  t)
          (values nil nil)))))

(defclass reference-backend (sat-backend)
  ((propagate :initarg :propagate :initform nil :reader reference-backend-propagate
              :documentation "0.2: unit propagation before each decision (see REFERENCE-SEARCH)."))
  (:documentation "Test oracle: cl-repository's naive search over CNF (with
:PROPAGATE T, plus unit propagation)."))

(defmethod backend-solve ((backend reference-backend) cnf &key assumptions order phase budget)
  (reference-search (cnf-clauses cnf)
                    :assumptions assumptions :order order :phase phase :budget budget
                    :propagate (reference-backend-propagate backend)))
