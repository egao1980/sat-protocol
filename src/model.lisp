;;;; Models and lazy model sequences. Bodies are stubs.
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
  (declare (ignore model name))
  (%sat-pending 'model-value))

(defun next-model (sequence)
  (declare (ignore sequence))
  (%sat-pending 'next-model))

(defun collect-models (sequence)
  (declare (ignore sequence))
  (%sat-pending 'collect-models))
