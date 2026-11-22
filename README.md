# sat-protocol

Propositional satisfiability for [cl-stack](https://github.com/egao1980/cl-stack): a formula model, CNF conversion (Tseitin), DIMACS read/write, and a CLOS solver protocol with `solve`, `solve-all`, `minimize` (weighted preferences), assumptions, unsat cores and pluggable decision order. Errors are CLHS conditions with restarts.

**Status:** planned (slice L2, Track L). Brief: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). First backend: [`sat-backend-dpll`](https://github.com/egao1980/sat-backend-dpll). Independent of logic-protocol.

## License

MIT, see [LICENSE](LICENSE).
