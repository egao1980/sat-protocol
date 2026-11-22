;;;; CNF: clauses over integer literals (DIMACS style) plus a variable table.
;;;; Class shape GIVEN; bodies are stubs.
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

(defun copy-cnf (cnf) (declare (ignore cnf)) (%sat-pending 'copy-cnf))
(defun cnf-clauses (cnf) (declare (ignore cnf)) (%sat-pending 'cnf-clauses))
(defun cnf-clause-count (cnf) (declare (ignore cnf)) (%sat-pending 'cnf-clause-count))
(defun cnf-variable-count (cnf) (declare (ignore cnf)) (%sat-pending 'cnf-variable-count))
(defun cnf-ensure-variable (cnf name)
  (declare (ignore cnf name)) (%sat-pending 'cnf-ensure-variable))
(defun cnf-variable-index (cnf name)
  (declare (ignore cnf name)) (%sat-pending 'cnf-variable-index))
(defun cnf-variable-name (cnf index)
  (declare (ignore cnf index)) (%sat-pending 'cnf-variable-name))
(defun cnf-aux-variable-p (cnf index)
  (declare (ignore cnf index)) (%sat-pending 'cnf-aux-variable-p))
(defun cnf-user-variables (cnf) (declare (ignore cnf)) (%sat-pending 'cnf-user-variables))
(defun cnf-literal (cnf literal)
  (declare (ignore cnf literal)) (%sat-pending 'cnf-literal))
(defun cnf-add-clause (cnf literals)
  (declare (ignore cnf literals)) (%sat-pending 'cnf-add-clause))

(defun to-cnf (formula &key cnf)
  (declare (ignore formula cnf))
  (%sat-pending 'to-cnf))
