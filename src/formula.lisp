;;;; Propositional formulas with constant folding (cl-repository's simplifying
;;;; constructors, generalised). Class and GF shapes are GIVEN.
;;;;
;;;; Variables are named by any object other than NIL, compared with EQUAL
;;;; (strings, integers, symbols, keywords, lists). Formulas are immutable.
;;;;
;;;; FORMULA-OPERATOR is one of :TRUE :FALSE :VAR :NOT :AND :OR :IMPLIES :IFF,
;;;; and (0.2) :AT-MOST.
;;;; FORMULA-OPERANDS: NIL for constants and variables, (F) for :NOT, the
;;;; children for :AND / :OR (two or more), (P Q) for :IMPLIES / :IFF, the
;;;; literal formulas for :AT-MOST (one or more, given order, duplicates kept).
;;;;
;;;; :AT-MOST (0.2, GIVEN shape; built only by the constructors in
;;;; cardinality.lisp) is the linear constraint
;;;;     sum of w_i over the operands L_i that are true  <=  K
;;;; FORMULA-WEIGHTS: the positive integers w_i, parallel to FORMULA-OPERANDS
;;;; (all 1 for a cardinality constraint). FORMULA-BOUND: K, an integer with
;;;; 1 <= K < sum of the weights (the constructors fold every other case).
;;;; FORMULA-ENCODING: how TO-CNF encodes it, one of :PAIRWISE :SEQUENTIAL
;;;; :TOTALIZER :BDD (never :AUTO: the constructor resolves it). The three
;;;; readers return NIL for every other operator. The encoding never changes
;;;; the formula's meaning: FORMULA-EVAL, FORMULA-VARIABLES, FORMULA-ASSIGN and
;;;; the sexp ignore it.
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
;;;; :AT-MOST (0.2): true when the weights of its true operands sum to at most
;;;; FORMULA-BOUND.
;;;;
;;;; FORMULA-ASSIGN formula name value: substitute the constant VALUE (boolean)
;;;; for every occurrence of NAME, rebuilding through the folding constructors
;;;; (cl-repository's SAT-REPLACE). An :AT-MOST node is rebuilt with
;;;; SAT-PB-AT-MOST over its (weight . operand) terms, its bound and its
;;;; encoding, so a substituted operand folds by the rules in cardinality.lisp.
;;;;
;;;; Sexp syntax (FORMULA->SEXP / SEXP->FORMULA), for fixtures and printing:
;;;;   :true :false | (:var NAME) | (:not S) | (:and S...) | (:or S...)
;;;;   | (:implies P Q) | (:iff P Q) | NAME
;;;;   | (:at-most K S...)               (0.2) SAT-AT-MOST-K over the S
;;;;   | (:pb-at-most K (W S)...)        (0.2) SAT-PB-AT-MOST over ((W . S)...)
;;;; FORMULA->SEXP writes an :AT-MOST node as (:at-most K S...) when every
;;;; weight is 1, else as (:pb-at-most K (W S)...); the encoding is not written
;;;; (SEXP->FORMULA uses :AUTO). SEXP->FORMULA: K must be an integer, each W a
;;;; non-negative integer and each S a literal sexp (NAME, (:var NAME),
;;;; (:not NAME), (:not (:var NAME))) or :true / :false; anything else is a
;;;; malformed sexp (SAT-INVALID-FORMULA with USE-VALUE, as below).
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
             :type (member :true :false :var :not :and :or :implies :iff :at-most))
   (operands :initarg :operands :reader formula-operands :initform nil :type list)
   (name :initarg :name :initform nil :reader %formula-name)
   ;; 0.2, :AT-MOST only (NIL otherwise).
   (bound :initarg :bound :initform nil :reader formula-bound
          :documentation ":AT-MOST: the integer K.")
   (weights :initarg :weights :initform nil :reader formula-weights
            :documentation ":AT-MOST: positive integers parallel to the operands.")
   (encoding :initarg :encoding :initform nil :reader formula-encoding
             :documentation ":AT-MOST: :PAIRWISE, :SEQUENTIAL, :TOTALIZER or :BDD."))
  (:documentation "An immutable propositional formula. Build it with the
constructors (SAT-VAR, SAT-AND, ..., SAT-PB-AT-MOST), never with MAKE-INSTANCE."))

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

(defun %make-at-most (operands weights bound encoding)
  "0.2, GIVEN: the raw :AT-MOST node (no checks, no folding). The constructors
in cardinality.lisp call it once they have folded and resolved ENCODING."
  (make-instance 'formula :operator :at-most :operands operands
                          :weights weights :bound bound :encoding encoding))

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
                 (:iff (eq (ev (first args)) (ev (second args))))
                 ;; Every operand is evaluated (an unbound one signals as usual).
                 (:at-most (<= (loop for weight in (formula-weights f)
                                     for operand in args
                                     when (ev operand) sum weight)
                               (formula-bound f)))))))
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
                 (:iff (sat-iff (walk (first args)) (walk (second args))))
                 (:at-most (sat-pb-at-most (mapcar #'cons (formula-weights f) (mapcar #'walk args))
                                           (formula-bound f)
                                           :encoding (formula-encoding f)))))))
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
       (cons (formula-operator f) (mapcar #'formula->sexp (formula-operands f))))
      (:at-most
       (let ((weights (formula-weights f))
             (operands (mapcar #'formula->sexp (formula-operands f))))
         (if (every (lambda (w) (eql w 1)) weights)
             (list* :at-most (formula-bound f) operands)
             (list* :pb-at-most (formula-bound f) (mapcar #'list weights operands))))))))

(defun %proper-list-p (object)
  "True for a finite, NIL-terminated list (tortoise and hare)."
  (let ((slow object) (fast object))
    (loop
      (cond ((null fast) (return t)) ((atom fast) (return nil)))
      (setf fast (cdr fast))
      (cond ((null fast) (return t)) ((atom fast) (return nil)))
      (setf fast (cdr fast) slow (cdr slow))
      (when (eq fast slow) (return nil)))))

(defun %literal-sexp-p (sexp)
  "0.2: an operand of (:at-most ...) / (:pb-at-most ...): NAME, (:var NAME),
(:not NAME), (:not (:var NAME)), :true or :false. A bare NAME is an atom other
than NIL, :TRUE and :FALSE; (:var NAME) takes any non-NIL name."
  (flet ((name-p (s) (and s (atom s) (not (member s '(:true :false)))))
         (var-p (s) (and (consp s) (%proper-list-p s) (eq (first s) :var)
                         (= 2 (length s)) (second s) t)))
    (or (member sexp '(:true :false))
        (name-p sexp)
        (var-p sexp)
        (and (consp sexp) (%proper-list-p sexp) (eq (first sexp) :not) (= 2 (length sexp))
             (or (name-p (second sexp)) (var-p (second sexp)))))))

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
                 ;; 0.2: every part is checked here, before any constructor runs,
                 ;; so a malformed constraint signals SAT-INVALID-FORMULA (with
                 ;; USE-VALUE at this node), never TYPE-ERROR.
                 ((:at-most :pb-at-most)
                  (unless (and args (integerp (first args)))
                    (bad (format nil "~S needs an integer bound" (first sexp))))
                  (let ((k (first args)) (operands (rest args)))
                    (if (eq (first sexp) :at-most)
                        (progn
                          (dolist (s operands)
                            (unless (%literal-sexp-p s)
                              (bad "an :at-most operand must be a literal sexp")))
                          (sat-at-most-k (mapcar #'sexp->formula operands) k))
                        (progn
                          (dolist (term operands)
                            (unless (and (consp term) (%proper-list-p term) (= 2 (length term))
                                         (typep (first term) '(integer 0 *))
                                         (%literal-sexp-p (second term)))
                              (bad "a :pb-at-most term must be (WEIGHT LITERAL), WEIGHT >= 0")))
                          (sat-pb-at-most (mapcar (lambda (term)
                                                    (cons (first term) (sexp->formula (second term))))
                                                  operands)
                                          k)))))
                 (t (bad "unknown operator")))))))))
