;;;; Propositional formulas with constant folding (cl-repository's simplifying
;;;; constructors, generalised). Class and GF shapes are GIVEN.
;;;;
;;;; Variables are named by any object other than NIL, compared with EQUAL
;;;; (strings, integers, symbols, keywords, lists). Formulas are immutable.
;;;;
;;;; FORMULA-OPERATOR is one of :TRUE :FALSE :VAR :NOT :AND :OR :IMPLIES :IFF.
;;;; FORMULA-OPERANDS: NIL for constants and variables, (F) for :NOT, the
;;;; children for :AND / :OR (two or more), (P Q) for :IMPLIES / :IFF.
;;;;
;;;; Constructors fold constants (exact rules; the tests check them):
;;;;   (sat-true) (sat-false)       the two constants (each call may return the
;;;;                                same object).
;;;;   (sat-var name)               NAME NIL -> SAT-INVALID-FORMULA (USE-VALUE: a
;;;;                                replacement name).
;;;;   (sat-not f)                  true <-> false; (not (not x)) -> x.
;;;;   (sat-and &rest fs) / (sat-and* list)
;;;;                                nested :AND children are spliced in place
;;;;                                (flattened); true children dropped; any false
;;;;                                child -> false; no children -> true; one child
;;;;                                -> that child. Order and duplicates are kept.
;;;;   (sat-or &rest fs) / (sat-or* list)   the dual.
;;;;   (sat-implies p q)            p false -> true; p true -> q; q true -> true;
;;;;                                q false -> (sat-not p); else :IMPLIES.
;;;;   (sat-iff p q)                p true -> q; p false -> (sat-not q); q true -> p;
;;;;                                q false -> (sat-not p); else :IFF.
;;;; Every operand must be a FORMULA; anything else signals SAT-INVALID-FORMULA
;;;; with DATUM = the operand inside RESTART-CASE with USE-VALUE (a replacement
;;;; formula, checked again).
;;;;
;;;; A literal is a :VAR formula or the :NOT of one. Where an API takes literals
;;;; (assumptions, objective entries) a bare variable name means the positive
;;;; literal.
;;;;
;;;; FORMULA-VARIABLES: variable names in first-occurrence order (depth-first,
;;;; operands left to right), no duplicates (EQUAL).
;;;;
;;;; FORMULA-EVAL formula assignment &key default: T or NIL. ASSIGNMENT is an
;;;; alist ((name . boolean) ...), a hash table (EQUAL test) or a function
;;;; name -> (values value bound-p). An unbound variable takes DEFAULT when
;;;; :DEFAULT is supplied, else signals SAT-UNBOUND-VARIABLE with USE-VALUE.
;;;;
;;;; FORMULA-ASSIGN formula name value: substitute the constant VALUE (boolean)
;;;; for every occurrence of NAME, rebuilding through the folding constructors
;;;; (cl-repository's SAT-REPLACE).
;;;;
;;;; Sexp syntax (FORMULA->SEXP / SEXP->FORMULA), for fixtures and printing:
;;;;   :true :false | (:var NAME) | (:not S) | (:and S...) | (:or S...)
;;;;   | (:implies P Q) | (:iff P Q) | NAME
;;;; A bare NAME is any atom other than NIL, :TRUE and :FALSE (strings,
;;;; integers, symbols, other keywords). FORMULA->SEXP writes a bare name for
;;;; strings, integers and non-keyword symbols other than T, and (:var NAME)
;;;; otherwise. SEXP->FORMULA goes through the folding constructors, so
;;;; (formula->sexp (sexp->formula S)) is S folded; a malformed sexp (unknown
;;;; operator, wrong arity, NIL) signals SAT-INVALID-FORMULA with USE-VALUE (a
;;;; replacement sexp). PRINT-OBJECT of a formula is #<FORMULA sexp>, the sexp
;;;; written with PRIN1.

(in-package #:sat-protocol)

(defclass formula ()
  ((operator :initarg :operator :reader formula-operator
             :type (member :true :false :var :not :and :or :implies :iff))
   (operands :initarg :operands :reader formula-operands :initform nil :type list)
   (name :initarg :name :initform nil :reader %formula-name))
  (:documentation "An immutable propositional formula. Build it with the
constructors (SAT-VAR, SAT-AND, ...), never with MAKE-INSTANCE."))

(defun formula-p (object)
  (typep object 'formula))

(defmethod print-object ((f formula) stream)
  ;; #<FORMULA sexp>. A constructed formula always converts; the slot check
  ;; keeps printing safe on a bare MAKE-INSTANCE (printing must never signal).
  (print-unreadable-object (f stream :type t)
    (if (slot-boundp f 'operator)
        (prin1 (formula->sexp f) stream)
        (write-string "(uninitialised)" stream))))

(defun %make-formula (operator operands)
  (make-instance 'formula :operator operator :operands operands))

(defvar *%true* (make-instance 'formula :operator :true))
(defvar *%false* (make-instance 'formula :operator :false))

(defun %read-value ()
  (format *query-io* "Value: ")
  (force-output *query-io*)
  (list (read *query-io*)))

(defun %check-formula (object)
  "OBJECT, or the USE-VALUE replacement (checked again), as a FORMULA."
  (loop
    (when (formula-p object) (return object))
    (restart-case (error 'sat-invalid-formula :datum object :message "not a formula")
      (use-value (value)
        :report "Use another formula (checked again)."
        :interactive %read-value
        (setf object value)))))

(defun sat-true () *%true*)
(defun sat-false () *%false*)

(defun sat-var (name)
  (loop
    (when name
      (return (make-instance 'formula :operator :var :name name)))
    (restart-case (error 'sat-invalid-formula :datum name :message "a variable name cannot be NIL")
      (use-value (value)
        :report "Use another variable name (checked again)."
        :interactive %read-value
        (setf name value)))))

(defun sat-not (formula)
  (let ((f (%check-formula formula)))
    (case (formula-operator f)
      (:true (sat-false))
      (:false (sat-true))
      (:not (first (formula-operands f)))
      (t (%make-formula :not (list f))))))

(defun %fold-nary (operator identity absorbing formulas)
  "Fold an :AND (identity :TRUE, absorbing :FALSE) or :OR (the dual). Every
operand is checked before any folding."
  (let ((checked (mapcar #'%check-formula formulas))
        (children '()))
    (dolist (f checked)
      (let ((op (formula-operator f)))
        (cond ((eq op identity))
              ((eq op absorbing)
               (return-from %fold-nary (if (eq absorbing :false) (sat-false) (sat-true))))
              ((eq op operator)
               (dolist (k (formula-operands f)) (push k children)))
              (t (push f children)))))
    (setf children (nreverse children))
    (cond ((null children) (if (eq identity :true) (sat-true) (sat-false)))
          ((null (rest children)) (first children))
          (t (%make-formula operator children)))))

(defun sat-and* (formulas) (%fold-nary :and :true :false formulas))
(defun sat-or* (formulas) (%fold-nary :or :false :true formulas))
(defun sat-and (&rest formulas) (sat-and* formulas))
(defun sat-or (&rest formulas) (sat-or* formulas))

(defun sat-implies (p q)
  (let ((p (%check-formula p))
        (q (%check-formula q)))
    (cond ((eq (formula-operator p) :false) (sat-true))
          ((eq (formula-operator p) :true) q)
          ((eq (formula-operator q) :true) (sat-true))
          ((eq (formula-operator q) :false) (sat-not p))
          (t (%make-formula :implies (list p q))))))

(defun sat-iff (p q)
  (let ((p (%check-formula p))
        (q (%check-formula q)))
    (cond ((eq (formula-operator p) :true) q)
          ((eq (formula-operator p) :false) (sat-not q))
          ((eq (formula-operator q) :true) p)
          ((eq (formula-operator q) :false) (sat-not p))
          (t (%make-formula :iff (list p q))))))

(defun sat-var-name (formula)
  "The name of a :VAR formula."
  (if (and (formula-p formula) (eq (formula-operator formula) :var))
      (%formula-name formula)
      (error 'sat-invalid-formula :datum formula :message "not a variable")))

(defun literal-p (object)
  "True when OBJECT is a :VAR formula or the :NOT of one."
  (and (formula-p object)
       (case (formula-operator object)
         (:var t)
         (:not (eq :var (formula-operator (first (formula-operands object)))))
         (t nil))))

(defun %check-literal (literal)
  (cond ((formula-p literal)
         (unless (literal-p literal)
           (error 'sat-invalid-formula :datum literal :message "not a literal"))
         literal)
        ((null literal)
         (error 'sat-invalid-formula :datum literal :message "a variable name cannot be NIL"))
        (t literal)))

(defun literal-name (literal)
  "The variable name of LITERAL (a literal formula or a bare name)."
  (let ((l (%check-literal literal)))
    (cond ((not (formula-p l)) l)
          ((eq (formula-operator l) :var) (%formula-name l))
          (t (%formula-name (first (formula-operands l)))))))

(defun literal-positive-p (literal)
  "NIL for a negated literal, else T (a bare name is positive)."
  (let ((l (%check-literal literal)))
    (not (and (formula-p l) (eq (formula-operator l) :not)))))

(defun formula-variables (formula)
  (let ((seen (make-hash-table :test 'equal))
        (names '()))
    (labels ((walk (f)
               (if (eq (formula-operator f) :var)
                   (let ((name (%formula-name f)))
                     (unless (gethash name seen)
                       (setf (gethash name seen) t)
                       (push name names)))
                   (mapc #'walk (formula-operands f)))))
      (walk (%check-formula formula)))
    (nreverse names)))

(defun formula-eval (formula assignment &key (default nil default-p))
  (labels ((lookup (name)
             (multiple-value-bind (value bound)
                 (cond ((functionp assignment) (funcall assignment name))
                       ((hash-table-p assignment) (gethash name assignment))
                       (t (let ((cell (assoc name assignment :test #'equal)))
                            (values (cdr cell) (and cell t)))))
               (cond (bound (and value t))
                     (default-p (and default t))
                     (t (restart-case (error 'sat-unbound-variable :name name)
                          (use-value (value)
                            :report "Use a value for this occurrence."
                            :interactive %read-value
                            (and value t)))))))
           (ev (f)
             (let ((args (formula-operands f)))
               (ecase (formula-operator f)
                 (:true t)
                 (:false nil)
                 (:var (lookup (%formula-name f)))
                 (:not (not (ev (first args))))
                 (:and (every #'ev args))
                 (:or (and (some #'ev args) t))
                 (:implies (or (not (ev (first args))) (ev (second args))))
                 (:iff (eq (ev (first args)) (ev (second args))))))))
    (ev (%check-formula formula))))

(defun formula-assign (formula name value)
  (labels ((walk (f)
             (let ((args (formula-operands f)))
               (ecase (formula-operator f)
                 ((:true :false) f)
                 (:var (if (equal name (%formula-name f))
                           (if value (sat-true) (sat-false))
                           f))
                 (:not (sat-not (walk (first args))))
                 (:and (sat-and* (mapcar #'walk args)))
                 (:or (sat-or* (mapcar #'walk args)))
                 (:implies (sat-implies (walk (first args)) (walk (second args))))
                 (:iff (sat-iff (walk (first args)) (walk (second args))))))))
    (walk (%check-formula formula))))

(defun %bare-name-p (name)
  (or (stringp name)
      (integerp name)
      (and (symbolp name) (not (keywordp name)) (not (eq name t)))))

(defun formula->sexp (formula)
  (let ((f (%check-formula formula)))
    (ecase (formula-operator f)
      (:true :true)
      (:false :false)
      (:var (let ((name (%formula-name f)))
              (if (%bare-name-p name) name (list :var name))))
      ((:not :and :or :implies :iff)
       (cons (formula-operator f) (mapcar #'formula->sexp (formula-operands f)))))))

(defun %proper-list-p (object)
  "True for a finite, NIL-terminated list (tortoise and hare)."
  (let ((slow object) (fast object))
    (loop
      (cond ((null fast) (return t)) ((atom fast) (return nil)))
      (setf fast (cdr fast))
      (cond ((null fast) (return t)) ((atom fast) (return nil)))
      (setf fast (cdr fast) slow (cdr slow))
      (when (eq fast slow) (return nil)))))

(defun sexp->formula (sexp)
  (flet ((bad (why)
           ;; The restart lives at this node: the replacement sexp replaces
           ;; only this subtree, and is parsed (and checked) again.
           (restart-case (error 'sat-invalid-formula :datum sexp :message why)
             (use-value (value)
               :report "Use a replacement sexp (checked again)."
               :interactive %read-value
               (return-from sexp->formula (sexp->formula value))))))
    (cond ((eq sexp :true) (sat-true))
          ((eq sexp :false) (sat-false))
          ((null sexp) (bad "NIL is not a formula"))
          ((atom sexp) (sat-var sexp))
          ((not (%proper-list-p sexp)) (bad "not a proper list"))
          (t
           (let ((args (rest sexp)))
             (flet ((arity (n)
                      (unless (= n (length args))
                        (bad (format nil "~S takes ~D operand~:P" (first sexp) n)))))
               (case (first sexp)
                 (:var (if (and (= 1 (length args)) (first args))
                           (sat-var (first args))
                           (bad "(:var NAME) needs one non-NIL name")))
                 (:not (arity 1) (sat-not (sexp->formula (first args))))
                 (:and (sat-and* (mapcar #'sexp->formula args)))
                 (:or (sat-or* (mapcar #'sexp->formula args)))
                 (:implies (arity 2)
                  (sat-implies (sexp->formula (first args)) (sexp->formula (second args))))
                 (:iff (arity 2)
                  (sat-iff (sexp->formula (first args)) (sexp->formula (second args))))
                 (t (bad "unknown operator")))))))))
