;;;; sat-protocol: propositional formulas, CNF, DIMACS and a CLOS SAT solver protocol.
;;;; Brief: cl-stack/docs/capabilities/logic.md (Track L: slice L2 = 0.1.0, slice L2b-1
;;;; = 0.2.0). No backend inside; no dependencies. Independent of logic-protocol.
;;;;
;;;; 0.2.0 (L2b-1) adds cardinality and pseudo-Boolean constraints (formula
;;;; operator :AT-MOST, CNF-ADD-*), MINIMIZE strategies, budgets, hints and
;;;; lexicographic objectives, and BACKEND-FINAL-CONFLICT. Every 0.1 call keeps
;;;; its meaning.
;;;;
;;;; 0.3.0 (L2b-2) adds incremental sessions (src/session.lisp): SAT-SESSION,
;;;; its front ends and the BACKEND-SESSION-* GFs, whose default methods solve
;;;; from scratch, plus the conditions SAT-SESSION-CLOSED and SAT-BUDGET-REACHED
;;;; (restart USE-BEST). Every 0.2 call keeps its meaning.

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
   #:sat-session-closed                 ; 0.3
   #:sat-session-closed-session         ; 0.3
   #:sat-budget-reached                 ; 0.3: not an error
   #:sat-budget-reached-budget          ; 0.3
   #:sat-budget-reached-cost            ; 0.3
   #:use-best                           ; 0.3

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
   #:unsat-core

   ;; incremental sessions (src/session.lisp, 0.3)
   #:sat-session
   #:make-sat-session
   #:with-sat-session
   #:close-session
   #:session-open-p
   #:session-backend
   #:session-backend-state
   #:session-variable-count
   #:session-cnf
   #:session-add-variables
   #:session-add-clauses
   #:session-solve
   #:session-minimize
   #:session-model
   #:session-unsat-core
   #:backend-session-open
   #:backend-session-add-clauses
   #:backend-session-solve
   #:backend-session-final-conflict
   #:backend-session-minimize
   #:backend-session-close))

(in-package #:sat-protocol)
