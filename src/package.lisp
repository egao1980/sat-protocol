;;;; sat-protocol: propositional formulas, CNF, DIMACS and a CLOS SAT solver protocol.
;;;; Brief: cl-stack/docs/capabilities/logic.md (Track L: slice L2 = 0.1.0, slice L2b-1
;;;; = 0.2.0). No backend inside; no dependencies. Independent of logic-protocol.
;;;;
;;;; 0.2.0 (L2b-1) adds cardinality and pseudo-Boolean constraints (formula
;;;; operator :AT-MOST, CNF-ADD-*), MINIMIZE strategies, budgets, hints and
;;;; lexicographic objectives, and BACKEND-FINAL-CONFLICT. Every 0.1 call keeps
;;;; its meaning.

(defpackage #:sat-protocol
  (:use #:cl)
  (:nicknames #:stack-sat)
  (:export
   ;; conditions + restarts (src/conditions.lisp)
   #:sat-error
   #:sat-error-message
   #:sat-invalid-formula
   #:sat-invalid-formula-datum
   #:sat-unbound-variable
   #:sat-unbound-variable-name
   #:sat-no-backend
   #:sat-no-backend-formula
   #:sat-budget-exceeded
   #:sat-budget-exceeded-budget
   #:sat-budget-exceeded-timeout        ; 0.2
   #:sat-dimacs-error
   #:sat-dimacs-error-line
   #:sat-dimacs-error-line-number
   #:use-backend
   #:skip-line
   #:signal-budget-exceeded

   ;; formulas (src/formula.lisp)
   #:formula
   #:formula-p
   #:sat-true
   #:sat-false
   #:sat-var
   #:sat-not
   #:sat-and
   #:sat-or
   #:sat-and*
   #:sat-or*
   #:sat-implies
   #:sat-iff
   #:formula-operator
   #:formula-operands
   #:formula-bound                      ; 0.2: :AT-MOST nodes
   #:formula-weights                    ; 0.2
   #:formula-encoding                   ; 0.2
   #:sat-var-name
   #:literal-p
   #:literal-name
   #:literal-positive-p
   #:formula-variables
   #:formula-eval
   #:formula-assign
   #:formula->sexp
   #:sexp->formula

   ;; CNF (src/cnf.lisp)
   #:cnf
   #:cnf-p
   #:make-cnf
   #:copy-cnf
   #:to-cnf
   #:cnf-clauses
   #:cnf-clause-count
   #:cnf-variable-count
   #:cnf-add-clause
   #:cnf-ensure-variable
   #:cnf-variable-index
   #:cnf-variable-name
   #:cnf-aux-variable-p
   #:cnf-user-variables
   #:cnf-literal

   ;; cardinality and pseudo-Boolean constraints (src/cardinality.lisp, 0.2)
   #:sat-at-most-one
   #:sat-exactly-one
   #:sat-at-most-k
   #:sat-at-least-k
   #:sat-pb-at-most
   #:cnf-add-at-most-one
   #:cnf-add-exactly-one
   #:cnf-add-at-most-k
   #:cnf-add-at-least-k
   #:cnf-add-pb-at-most

   ;; DIMACS (src/dimacs.lisp)
   #:read-dimacs
   #:write-dimacs

   ;; models (src/model.lisp)
   #:model-value
   #:model-sequence
   #:next-model
   #:collect-models

   ;; backends and front ends (src/protocol.lisp; strategies in src/minimize.lisp)
   #:*sat-backend*
   #:sat-backend
   #:backend-solve
   #:backend-solve-all
   #:backend-minimize
   #:backend-unsat-core
   #:backend-final-conflict             ; 0.2
   #:solve
   #:solve-all
   #:minimize
   #:unsat-core))

(in-package #:sat-protocol)

(defun %l2b1-pending (name)
  "Contract stub for sat-protocol 0.2.0 (Track L, slice L2b-1). Every call is
replaced by the implementation, then this function is deleted. Signals a
SIMPLE-ERROR (deliberately not a SAT-ERROR, so no negative test passes on a
stub)."
  (error "sat-protocol 0.2 (L2b-1) pending: ~S" name))
