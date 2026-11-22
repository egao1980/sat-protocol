;;;; Models and lazy model sequences.
;;;;
;;;; A model is an alist ((name . boolean) ...) over user variables (never
;;;; Tseitin auxiliaries), in CNF index order: for a formula that is
;;;; FORMULA-VARIABLES order, then variables first seen in assumptions or an
;;;; objective. Values are exactly T or NIL.
;;;;
;;;; (model-value model name) -> (values value bound-p).
;;;;
;;;; MODEL-SEQUENCE is what SOLVE-ALL returns: a lazy, single-pass sequence.
;;;; (next-model seq) -> (values model T), or (values NIL NIL) once exhausted
;;;;   (and on every later call). Each call does only the search for that model.
;;;; (collect-models seq) -> list of the remaining models, in NEXT-MODEL order.

(in-package #:sat-protocol)

(defclass model-sequence ()
  ((generator :initarg :generator :reader %model-sequence-generator
              :documentation "Function of no arguments: (values model T) or (values NIL NIL).")
   (done :initform nil :accessor %model-sequence-done))
  (:documentation "Lazy sequence of models, from SOLVE-ALL."))

(defun model-value (model name)
  (let ((cell (assoc name model :test #'equal)))
    (if cell
        (values (cdr cell) t)
        (values nil nil))))

(defun next-model (sequence)
  (if (%model-sequence-done sequence)
      (values nil nil)
      (let ((more nil))
        (unwind-protect
             (multiple-value-bind (model ok)
                 (catch '%sat-front-value
                   (funcall (%model-sequence-generator sequence)))
               (setf more ok)
               (values model ok))
          ;; Exhaustion, a USE-VALUE exit and any non-local exit end the
          ;; sequence: a half-run generator is never re-entered.
          (unless more
            (setf (%model-sequence-done sequence) t))))))

(defun collect-models (sequence)
  (let ((models '()))
    (loop
      (multiple-value-bind (model ok) (next-model sequence)
        (unless ok (return (nreverse models)))
        (push model models)))))
