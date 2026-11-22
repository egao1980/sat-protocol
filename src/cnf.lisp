;;;; CNF: clauses over integer literals (DIMACS style) plus a variable table.
;;;; Class shape GIVEN.
;;;;
;;;; Variables are indexed 1..(CNF-VARIABLE-COUNT cnf). An index either names a
;;;; user variable (any non-NIL object, EQUAL) or is auxiliary (Tseitin; name
;;;; NIL). A literal is +i (variable i true) or -i (false).
;;;;
;;;; (make-cnf)                    empty CNF.
;;;; (copy-cnf cnf)                independent copy (adding to one never changes
;;;;                               the other).
;;;; (cnf-clauses cnf)             fresh list of clauses, each a fresh list of
;;;;                               integers, in the order added, literals as given.
;;;; (cnf-clause-count cnf) (cnf-variable-count cnf)
;;;; (cnf-ensure-variable cnf name) index of NAME, allocating the next index when
;;;;                               absent. NAME NIL allocates a fresh auxiliary.
;;;; (cnf-variable-index cnf name) index or NIL.
;;;; (cnf-variable-name cnf index) name, or NIL for an auxiliary.
;;;; (cnf-aux-variable-p cnf index)
;;;; (cnf-user-variables cnf)      user names in index order.
;;;; (cnf-literal cnf literal)     integer for a literal (formula or bare name),
;;;;                               allocating the variable when absent. A formula
;;;;                               that is not a literal signals
;;;;                               SAT-INVALID-FORMULA.
;;;; (cnf-add-clause cnf ints)     append one clause; returns CNF. A literal that
;;;;                               is 0, not an integer, or beyond
;;;;                               CNF-VARIABLE-COUNT signals SAT-INVALID-FORMULA
;;;;                               (DATUM = that literal) and adds nothing. The
;;;;                               empty clause is allowed (the CNF is then UNSAT).
;;;;
;;;; (to-cnf formula &key cnf)     clauses for FORMULA added to CNF (a fresh one
;;;;   when NIL); returns the CNF. FORMULA may also be a CNF: then it is returned
;;;;   as is (no copy) when :CNF is NIL. User variables are allocated first, in
;;;;   FORMULA-VARIABLES order, so a fresh CNF has them at 1..k.
;;;;   Clause-shaped input gets NO auxiliary variables. Taking the top-level
;;;;   conjuncts in order (a non-:AND formula is one conjunct), each conjunct
;;;;   becomes exactly one clause when it is:
;;;;     a literal L                        -> (L)
;;;;     (:or L1 ... Ln) of literals        -> (L1 ... Ln)
;;;;     (:not (:and L1 ... Ln)) of literals-> (-L1 ... -Ln)
;;;;     (:implies L Q), Q a literal or an :or of literals
;;;;                                        -> (-L Q1 ... Qn)
;;;;   :true adds nothing; :false adds the empty clause. Any other conjunct is
;;;;   encoded with Tseitin (or Plaisted-Greenbaum) auxiliaries: the result is
;;;;   equisatisfiable, its models projected on the user variables are exactly
;;;;   the models of FORMULA, and the number of auxiliaries is at most the number
;;;;   of operator nodes of FORMULA.

(in-package #:sat-protocol)

(defclass cnf ()
  ((names :initform (make-array 0 :adjustable t :fill-pointer t) :reader %cnf-names
          :documentation "Element i-1 is the name of variable i, or NIL.")
   (index :initform (make-hash-table :test 'equal) :reader %cnf-index
          :documentation "name -> index.")
   (clauses :initform nil :accessor %cnf-clauses
            :documentation "Clauses in any internal order/representation."))
  (:documentation "Clauses over integer literals plus a variable table."))

(defmethod print-object ((c cnf) stream)
  (print-unreadable-object (c stream :type t :identity t)
    (format stream "~D var~:P" (length (%cnf-names c)))))

(defun cnf-p (object) (typep object 'cnf))

(defun make-cnf () (make-instance 'cnf))

;;; Clause store: %CNF-CLAUSES is NIL or an adjustable vector (fill pointer) of
;;; clause lists. Stored clauses are private copies and never mutated, so
;;; COPY-CNF may share them.

(defun %clause-vector (cnf)
  (or (%cnf-clauses cnf)
      (setf (%cnf-clauses cnf) (make-array 8 :adjustable t :fill-pointer 0))))

(defun copy-cnf (cnf)
  (let ((copy (make-cnf)))
    (loop for name across (%cnf-names cnf)
          do (vector-push-extend name (%cnf-names copy)))
    (maphash (lambda (name index) (setf (gethash name (%cnf-index copy)) index))
             (%cnf-index cnf))
    (let ((clauses (%cnf-clauses cnf)))
      (when clauses
        (let ((v (%clause-vector copy)))
          (loop for c across clauses do (vector-push-extend c v)))))
    copy))

(defun cnf-clauses (cnf)
  (let ((clauses (%cnf-clauses cnf)))
    (and clauses (map 'list #'copy-list clauses))))

(defun cnf-clause-count (cnf)
  (let ((clauses (%cnf-clauses cnf)))
    (if clauses (fill-pointer clauses) 0)))

(defun cnf-variable-count (cnf)
  (fill-pointer (%cnf-names cnf)))

(defun cnf-ensure-variable (cnf name)
  (or (and name (gethash name (%cnf-index cnf)))
      (let ((index (1+ (vector-push-extend name (%cnf-names cnf)))))
        (when name
          (setf (gethash name (%cnf-index cnf)) index))
        index)))

(defun cnf-variable-index (cnf name)
  (and name (values (gethash name (%cnf-index cnf)))))

(defun %check-index (cnf index)
  (unless (and (integerp index) (<= 1 index (cnf-variable-count cnf)))
    (error 'sat-error :message (format nil "~S is not a variable index of ~S" index cnf)))
  index)

(defun cnf-variable-name (cnf index)
  (aref (%cnf-names cnf) (1- (%check-index cnf index))))

(defun cnf-aux-variable-p (cnf index)
  (null (cnf-variable-name cnf index)))

(defun cnf-user-variables (cnf)
  (loop for name across (%cnf-names cnf) when name collect name))

(defun cnf-literal (cnf literal)
  (let ((index (cnf-ensure-variable cnf (literal-name literal))))
    (if (literal-positive-p literal) index (- index))))

(defun cnf-add-clause (cnf literals)
  (unless (listp literals)
    (error 'sat-invalid-formula :datum literals :message "a clause is a list of integer literals"))
  (let ((n (cnf-variable-count cnf)))
    (dolist (l literals)
      (unless (and (integerp l) (/= l 0) (<= (abs l) n))
        (error 'sat-invalid-formula :datum l :message "not a literal of this CNF")))
    (vector-push-extend (copy-list literals) (%clause-vector cnf))
    cnf))

;;; Encoder. User variables first; then per top-level conjunct either the
;;; clause-shaped fast path or Plaisted-Greenbaum. GUARD (an integer literal or
;;; NIL) prefixes every top-level clause with -GUARD ("GUARD -> conjunct"); the
;;; selectors of UNSAT-CORE's NAMED formulas use it.

(defun %lit (cnf literal)
  "Integer for a literal formula whose variable is already allocated."
  (cnf-literal cnf literal))

(defun %clause-shape (cnf conjunct)
  "The one clause for a clause-shaped CONJUNCT, or :NONE."
  (flet ((lits (fs)
           (if (every #'literal-p fs)
               (mapcar (lambda (x) (%lit cnf x)) fs)
               :none)))
    (let ((args (formula-operands conjunct)))
      (case (formula-operator conjunct)
        (:var (list (%lit cnf conjunct)))
        (:not (let ((x (first args)))
                (cond ((literal-p conjunct) (list (%lit cnf conjunct)))
                      ((eq (formula-operator x) :and)
                       (let ((ls (lits (formula-operands x))))
                         (if (eq ls :none) :none (mapcar #'- ls))))
                      (t :none))))
        (:or (lits args))
        (:implies (destructuring-bind (p q) args
                    (let ((qs (cond ((literal-p q) (list q))
                                    ((eq (formula-operator q) :or) (formula-operands q)))))
                      (if (and (literal-p p) qs (every #'literal-p qs))
                          (cons (- (%lit cnf p)) (lits qs))
                          :none))))
        (t :none)))))

(defun %pg (cnf f pos neg)
  "Plaisted-Greenbaum: an integer literal X for F, with clauses X -> F when POS
and F -> X when NEG. One auxiliary per :AND/:OR/:IMPLIES/:IFF node, none for
:NOT or :VAR. Children are encoded before their parent's auxiliary is
allocated (post-order), so definitions are complete below each auxiliary."
  (let ((args (formula-operands f)))
    (ecase (formula-operator f)
      (:var (cnf-ensure-variable cnf (%formula-name f)))
      (:not (- (%pg cnf (first args) neg pos)))
      ((:and :or)
       (let* ((ks (mapcar (lambda (k) (%pg cnf k pos neg)) args))
              (x (cnf-ensure-variable cnf nil)))
         (if (eq (formula-operator f) :and)
             (progn
               (when pos (dolist (k ks) (cnf-add-clause cnf (list (- x) k))))
               (when neg (cnf-add-clause cnf (cons x (mapcar #'- ks)))))
             (progn
               (when pos (cnf-add-clause cnf (cons (- x) ks)))
               (when neg (dolist (k ks) (cnf-add-clause cnf (list x (- k)))))))
         x))
      (:implies
       (let* ((lp (%pg cnf (first args) neg pos))
              (lq (%pg cnf (second args) pos neg))
              (x (cnf-ensure-variable cnf nil)))
         (when pos (cnf-add-clause cnf (list (- x) (- lp) lq)))
         (when neg
           (cnf-add-clause cnf (list x lp))
           (cnf-add-clause cnf (list x (- lq))))
         x))
      (:iff
       (let* ((lp (%pg cnf (first args) t t))
              (lq (%pg cnf (second args) t t))
              (x (cnf-ensure-variable cnf nil)))
         (when pos
           (cnf-add-clause cnf (list (- x) (- lp) lq))
           (cnf-add-clause cnf (list (- x) lp (- lq))))
         (when neg
           (cnf-add-clause cnf (list x lp lq))
           (cnf-add-clause cnf (list x (- lp) (- lq))))
         x)))))

(defun %add-formula (cnf formula &optional guard)
  (dolist (name (formula-variables formula))
    (cnf-ensure-variable cnf name))
  (flet ((emit (clause)
           (cnf-add-clause cnf (if guard (cons (- guard) clause) clause))))
    (dolist (c (if (eq (formula-operator formula) :and)
                   (formula-operands formula)
                   (list formula)))
      (case (formula-operator c)
        (:true)
        (:false (emit '()))
        (t (let ((shape (%clause-shape cnf c)))
             (cond ((not (eq shape :none)) (emit shape))
                   ;; A top-level :OR needs no auxiliary of its own.
                   ((eq (formula-operator c) :or)
                    (emit (mapcar (lambda (k) (%pg cnf k t nil)) (formula-operands c))))
                   (t (emit (list (%pg cnf c t nil))))))))))
  cnf)

(defun %add-cnf (target source)
  "Add SOURCE's clauses to TARGET, user variables by name, auxiliaries fresh."
  (let ((map (make-array (1+ (cnf-variable-count source)) :initial-element 0)))
    (loop for i from 1 to (cnf-variable-count source)
          for name = (cnf-variable-name source i)
          when name do (setf (aref map i) (cnf-ensure-variable target name)))
    (loop for i from 1 to (cnf-variable-count source)
          unless (cnf-variable-name source i)
            do (setf (aref map i) (cnf-ensure-variable target nil)))
    (dolist (c (cnf-clauses source) target)
      (cnf-add-clause target (mapcar (lambda (l) (if (plusp l) (aref map l) (- (aref map (- l))))) c)))))

(defun to-cnf (formula &key cnf)
  (cond ((and (cnf-p formula) (null cnf)) formula)
        ((cnf-p formula) (%add-cnf cnf formula))
        (t (%add-formula (or cnf (make-cnf)) (%check-formula formula)))))
