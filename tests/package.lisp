;;;; sat-protocol/tests: the protocol's own tests, plus the conformance suite
;;;; run against REFERENCE-BACKEND (the test oracle; sat-protocol has no backend
;;;; inside). RUN-WITH-REFERENCE-BACKEND is what test-op calls.
;;;; 0.2 (L2b-1): cardinality-test (constraints and encodings) and
;;;; minimize-protocol-test (MINIMIZE / BACKEND-MINIMIZE / BACKEND-FINAL-CONFLICT
;;;; wiring). The whole run uses the reference search with unit propagation.

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
                #:chain-worst-labelling)
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
