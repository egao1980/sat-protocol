# sat-protocol

Propositional satisfiability for [cl-stack](https://github.com/egao1980/cl-stack): a formula model, CNF conversion (Tseitin), DIMACS read/write, and a CLOS solver protocol with `solve`, `solve-all`, `minimize` (weighted preferences), assumptions, unsat cores and pluggable decision order. Errors are CLHS conditions with restarts.

**Status:** 0.1.0 released (slice L2, Track L); **0.2.0 contracted** (slice L2b-1). Brief: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). First backend: [`sat-backend-dpll`](https://github.com/egao1980/sat-backend-dpll). Independent of logic-protocol.

0.2.0 adds cardinality and pseudo-Boolean constraints (`sat-at-most-one`, `sat-exactly-one`, `sat-at-most-k`, `sat-at-least-k`, `sat-pb-at-most` with `:encoding :pairwise | :sequential | :totalizer | :bdd`, and `cnf-add-*` over integer literals), `minimize` strategies (`:linear-bdd`, `:linear-totalizer`, `:stratified`, `:core-guided`), `:budget` / `:timeout` with a best-so-far result `(values model cost optimal-p)`, `:hint`, `:order` / `:phase`, lexicographic objectives `(:lex o1 o2 ...)`, and `backend-final-conflict` (a cheap core). Every 0.1 call keeps its meaning. The exact rules are in the headers of `src/cardinality.lisp`, `src/minimize.lisp` and `src/protocol.lisp`.

## Systems

- `sat-protocol`: formulas (`sat-var`, `sat-and`, ..., constant folding), CNF (`to-cnf`), cardinality constraints, DIMACS, models, the backend GFs and the front ends. No dependencies.
- `sat-protocol/conformance`: the Rove suite every backend runs on itself (`(sat-protocol/conformance:run-conformance backend)`), with `reference-backend`, a test oracle that ports cl-repository's naive search (`:propagate t` adds unit propagation), and the optimisation oracles (brute force, the weighted chain family and its dynamic-programming optimum).
- `sat-protocol/tests`: the protocol's own tests plus the conformance suite on `reference-backend` with unit propagation.

## License

MIT, see [LICENSE](LICENSE).
