(defsystem "sat-protocol"
  :version "0.1.0"
  :description "Propositional formulas, CNF (Tseitin), solve / solve-all / minimize, unsat cores and DIMACS behind a CLOS SAT solver protocol (stack-sat)"
  :author "egao1980"
  :license "MIT"
  :depends-on ()
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "conditions")
               (:file "formula")
               (:file "cnf")
               (:file "dimacs")
               (:file "model")
               (:file "protocol"))
  :in-order-to ((test-op (test-op "sat-protocol/tests"))))

;;; The backend conformance suite. Backend test systems depend on it and run
;;; it with their backend (sat-protocol/conformance:run-conformance).
(defsystem "sat-protocol/conformance"
  :depends-on ("sat-protocol" "rove")
  :pathname "tests/conformance"
  :serial t
  :components ((:file "package")
               (:file "reference")
               (:file "solve-test")
               (:file "solve-all-test")
               (:file "minimize-test")
               (:file "core-test")
               (:file "order-hook-test")
               (:file "budget-test")))

(defsystem "sat-protocol/tests"
  :depends-on ("sat-protocol" "sat-protocol/conformance" "rove")
  :pathname "tests"
  :serial t
  :components ((:file "package")
               (:file "formula-test")
               (:file "cnf-test")
               (:file "dimacs-test")
               (:file "backend-test"))
  :perform (test-op (o c)
             (unless (symbol-call :sat-protocol/tests :run-with-reference-backend)
               (error "tests failed for ~A" (component-name c)))))
