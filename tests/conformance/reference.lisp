;;;; REFERENCE-BACKEND: cl-repository's naive search (src/client/solver.lisp
;;;; SAT-SOLVE) over CNF, as a test oracle. No unit propagation, no learning:
;;;; at each node, a falsified clause fails; no clause without a true literal
;;;; succeeds; otherwise decide a candidate (ORDER, else the lowest index), try
;;;; PHASE's value (else T) first, then the other. Only for small instances.
;;;; GIVEN test code.

(in-package #:sat-protocol/conformance)

(defun reference-search (clauses &key assumptions order phase budget)
  "Search integer CLAUSES. Returns (values literals T) or (values NIL NIL)."
  (let ((assignment (make-hash-table))
        (decisions 0))
    (labels ((lit-value (lit)
               (multiple-value-bind (v bound) (gethash (abs lit) assignment)
                 (if bound (if (plusp lit) v (not v)) :free)))
             (candidates ()
               ;; :CONFLICT, or the ascending candidate list (NIL = all satisfied).
               (let ((cands nil))
                 (dolist (c clauses (sort (remove-duplicates cands) #'<))
                   (let ((satisfied nil) (free nil))
                     (dolist (l c)
                       (let ((v (lit-value l)))
                         (cond ((eq v :free) (push (abs l) free))
                               (v (setf satisfied t)))))
                     (unless satisfied
                       (if free
                           (setf cands (nconc free cands))
                           (return :conflict)))))))
             (search-node ()
               (let ((cands (candidates)))
                 (cond ((eq cands :conflict) nil)
                       ((null cands) t)
                       (t
                        (when (and budget (>= decisions budget))
                          (setf budget (signal-budget-exceeded budget)))
                        (incf decisions)
                        (let* ((var (if order (funcall order cands) (first cands)))
                               (first-value (if phase (and (funcall phase var) t) t)))
                          (dolist (value (list first-value (not first-value))
                                         (progn (remhash var assignment) nil))
                            (setf (gethash var assignment) value)
                            (when (search-node) (return t)))))))))
      (dolist (a assumptions)
        (let ((v (lit-value a)))
          (cond ((eq v :free) (setf (gethash (abs a) assignment) (plusp a)))
                ((not v) (return-from reference-search (values nil nil))))))
      (if (search-node)
          (values (loop for var being the hash-keys of assignment using (hash-value value)
                        collect (if value var (- var)))
                  t)
          (values nil nil)))))

(defclass reference-backend (sat-backend) ()
  (:documentation "Test oracle: cl-repository's naive search over CNF."))

(defmethod backend-solve ((backend reference-backend) cnf &key assumptions order phase budget)
  (reference-search (cnf-clauses cnf)
                    :assumptions assumptions :order order :phase phase :budget budget))
