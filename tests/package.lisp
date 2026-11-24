;;;; sat-protocol/tests: the protocol's own tests, plus the conformance suite
;;;; run against REFERENCE-BACKEND (the test oracle; sat-protocol has no backend
;;;; inside). RUN-WITH-REFERENCE-BACKEND is what test-op calls.
;;;; 0.2 (L2b-1): cardinality-test (constraints and encodings) and
;;;; minimize-protocol-test (MINIMIZE / BACKEND-MINIMIZE / BACKEND-FINAL-CONFLICT
;;;; wiring). The whole run uses the reference search with unit propagation.
;;;; 0.3 (L2b-2): session-protocol-test (the session GFs' call contract, the
;;;; stateless default methods against the fresh front ends, the stateful
;;;; session path on REFERENCE-SESSION-BACKEND, and every conformance session
;;;; check run a second time on it).

(defpackage #:sat-protocol/tests
  (:use #:cl #:rove #:sat-protocol)
  (:import-from #:sat-protocol/conformance
                #:reference-backend
                #:f
                #:make-rng
                #:rng-int
                #:random-sexp
                #:sexp-eval
                #:sexp-vars
                #:all-assignments
                #:clauses->cnf
                #:fixture-path
                ;; 0.2
                #:brute-models
                #:pigeonhole
                #:int-cost
                #:name-cost
                #:*strategies*
                #:random-chains
                #:chain-formula
                #:chain-objective
                #:chain-model
                #:chain-dp
                #:chain-labelling-cost
                #:chain-worst-labelling
                ;; 0.3
                #:reference-session-backend
                #:reference-session-clauses
                #:reference-session-calls
                #:session-from-clauses
                #:session-from-cnf
                #:index-objective
                #:literals->names
                #:model-satisfies-p
                #:brute-sat-over-p
                #:core-minimal-p
                #:run-session-checks
                #:random-clause*
                #:random-literals*
                #:random-3sat
                #:brute-satisfiable-p
                #:lit-formula
                #:int-objective->literals
                #:chain-session-fixture
                #:chain-lex-objective
                #:hint-chains)
  (:export #:run-with-reference-backend))

(in-package #:sat-protocol/tests)

(defun run-with-reference-backend (&key (style :spec))
  "Run sat-protocol/tests and sat-protocol/conformance (on REFERENCE-BACKEND
with unit propagation, 0.2) in one Rove run. Returns true when everything passes."
  (let ((*sat-backend* (make-instance 'reference-backend :propagate t)))
    (rove:run '("sat-protocol/conformance" "sat-protocol/tests") :style style)))

(defun sx (formula)
  "FORMULA->SEXP shorthand."
  (formula->sexp formula))

(defun fsx (sexp)
  "Fold SEXP through the constructors and print it back."
  (formula->sexp (sexp->formula sexp)))
