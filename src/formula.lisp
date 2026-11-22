;;;; Propositional formulas with constant folding (cl-repository's simplifying
;;;; constructors, generalised). Class and GF shapes are GIVEN; bodies are stubs.
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
  ;; Stub-safe placeholder (printing must never signal): the implementation
  ;; prints (formula->sexp f) here.
  (print-unreadable-object (f stream :type t)
    (prin1 (formula-operator f) stream)))

(defun sat-true () (%sat-pending 'sat-true))
(defun sat-false () (%sat-pending 'sat-false))
(defun sat-var (name) (declare (ignore name)) (%sat-pending 'sat-var))
(defun sat-not (formula) (declare (ignore formula)) (%sat-pending 'sat-not))
(defun sat-and* (formulas) (declare (ignore formulas)) (%sat-pending 'sat-and*))
(defun sat-or* (formulas) (declare (ignore formulas)) (%sat-pending 'sat-or*))
(defun sat-and (&rest formulas) (sat-and* formulas))
(defun sat-or (&rest formulas) (sat-or* formulas))
(defun sat-implies (p q) (declare (ignore p q)) (%sat-pending 'sat-implies))
(defun sat-iff (p q) (declare (ignore p q)) (%sat-pending 'sat-iff))

(defun sat-var-name (formula)
  "The name of a :VAR formula."
  (declare (ignore formula))
  (%sat-pending 'sat-var-name))

(defun literal-p (object)
  "True when OBJECT is a :VAR formula or the :NOT of one."
  (declare (ignore object))
  (%sat-pending 'literal-p))

(defun literal-name (literal)
  "The variable name of LITERAL (a literal formula or a bare name)."
  (declare (ignore literal))
  (%sat-pending 'literal-name))

(defun literal-positive-p (literal)
  "NIL for a negated literal, else T (a bare name is positive)."
  (declare (ignore literal))
  (%sat-pending 'literal-positive-p))

(defun formula-variables (formula)
  (declare (ignore formula))
  (%sat-pending 'formula-variables))

(defun formula-eval (formula assignment &key (default nil default-p))
  (declare (ignore formula assignment default default-p))
  (%sat-pending 'formula-eval))

(defun formula-assign (formula name value)
  (declare (ignore formula name value))
  (%sat-pending 'formula-assign))

(defun formula->sexp (formula)
  (declare (ignore formula))
  (%sat-pending 'formula->sexp))

(defun sexp->formula (sexp)
  (declare (ignore sexp))
  (%sat-pending 'sexp->formula))
