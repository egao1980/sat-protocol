# sat-protocol

Propositional satisfiability for [cl-stack](https://github.com/egao1980/cl-stack): a formula model, CNF conversion (Tseitin), DIMACS read/write, and a CLOS solver protocol with `solve`, `solve-all`, `minimize` (weighted preferences), assumptions, unsat cores and pluggable decision order. Errors are CLHS conditions with restarts.

**Status:** 0.1.0 released (slice L2, Track L); 0.2.0 (slice L2b-1); **0.3.0 contracted** (slice L2b-2, incremental sessions). Brief: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). First backend: [`sat-backend-dpll`](https://github.com/egao1980/sat-backend-dpll). Independent of logic-protocol.

0.2.0 adds cardinality and pseudo-Boolean constraints (`sat-at-most-one`, `sat-exactly-one`, `sat-at-most-k`, `sat-at-least-k`, `sat-pb-at-most` with `:encoding :pairwise | :sequential | :totalizer | :bdd`, and `cnf-add-*` over integer literals), `minimize` strategies (`:linear-bdd`, `:linear-totalizer`, `:stratified`, `:core-guided`), `:budget` / `:timeout` with a best-so-far result `(values model cost optimal-p)`, `:hint`, `:order` / `:phase`, lexicographic objectives `(:lex o1 o2 ...)`, and `backend-final-conflict` (a cheap core). Every 0.1 call keeps its meaning. The exact rules are in the headers of `src/cardinality.lisp`, `src/minimize.lisp` and `src/protocol.lisp`.

0.3.0 adds incremental sessions: one growing set of clauses over one backend, solved and minimised many times under per-call assumptions, at index level.

```lisp
(with-sat-session (s)                         ; :backend, else *sat-backend*
  (destructuring-bind (a b c) (session-add-variables s 3)
    (session-add-clauses s (list (list a b) (list (- a) c)))
    (session-add-clauses s (sat-at-most-one (mapcar #'sat-var (list b c))))
    (session-solve s :assumptions (list a))   ; => (1 -2 3), T
    (session-solve s :assumptions (list a (- c)))   ; => NIL, NIL
    (session-unsat-core s :minimal t)         ; => (1 -3), T
    (session-minimize s (list (cons 2 a) (cons 1 b)))))   ; => (-1 2 -3), 1, T
```

Every call answers as the fresh front-end call on `(session-cnf s)` with the same assumptions would. Clauses only grow; assumptions hold for one call. `session-model` and `session-unsat-core` describe the last answer. The backend GFs `backend-session-open`, `-add-clauses`, `-solve`, `-final-conflict`, `-minimize` and `-close` have default methods that re-solve from scratch, so every backend has sessions. A backend that keeps its own solver state (a stateful session) learns across calls, and `session-minimize` then runs its strategies through that state, with its bounds guarded by selector variables that are retired before it returns. With a `:budget`, a minimisation that has an incumbent signals `sat-budget-reached` (not an error): `use-best`, `continue` or `store-value`; unhandled, it returns the incumbent as `minimize` does. A closed session signals `sat-session-closed`. The rules are in the header of `src/session.lisp`.

## Systems

- `sat-protocol`: formulas (`sat-var`, `sat-and`, ..., constant folding), CNF (`to-cnf`), cardinality constraints, DIMACS, models, the backend GFs and the front ends. No dependencies.
- `sat-protocol/conformance`: the Rove suite every backend runs on itself (`(sat-protocol/conformance:run-conformance backend)`), with `reference-backend`, a test oracle that ports cl-repository's naive search (`:propagate t` adds unit propagation), and the optimisation oracles (brute force, the weighted chain family and its dynamic-programming optimum). 0.3: the session checks (against brute force and the fresh front ends) and `reference-session-backend`, a stateful session over the reference search.
- `sat-protocol/tests`: the protocol's own tests plus the conformance suite on `reference-backend` with unit propagation.

## License

MIT, see [LICENSE](LICENSE).
