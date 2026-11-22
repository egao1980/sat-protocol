(defsystem "sat-protocol"
  :version "0.1.0"
  :description "Propositional formulas, CNF (Tseitin), solve / solve-all / minimize, unsat cores and DIMACS behind a CLOS SAT solver protocol (stack-sat)"
  :author "egao1980"
  :license "MIT"
  :depends-on ()
  :serial t
  :pathname "src"
  :components ((:file "package")))
