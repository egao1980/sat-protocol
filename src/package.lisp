;;;; sat-protocol: propositional formulas, CNF, DIMACS and a CLOS SAT solver protocol.
;;;; Brief: cl-stack/docs/capabilities/logic.md (Track L, slice L2). No backend inside;
;;;; no dependencies. Independent of logic-protocol.

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

   ;; DIMACS (src/dimacs.lisp)
   #:read-dimacs
   #:write-dimacs

   ;; models (src/model.lisp)
   #:model-value
   #:model-sequence
   #:next-model
   #:collect-models

   ;; backends and front ends (src/protocol.lisp)
   #:*sat-backend*
   #:sat-backend
   #:backend-solve
   #:backend-solve-all
   #:backend-minimize
   #:backend-unsat-core
   #:solve
   #:solve-all
   #:minimize
   #:unsat-core))

(in-package #:sat-protocol)
