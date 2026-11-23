;;;; MINIMIZE 0.2 (Track L, slice L2b-1): strategies, budgets, hints and
;;;; lexicographic objectives. Specifies the front end MINIMIZE (protocol.lisp)
;;;; and the default method of BACKEND-MINIMIZE, which calls %MINIMIZE below
;;;; for every 0.2 argument. Signatures GIVEN; %MINIMIZE and the 0.2 path of
;;;; MINIMIZE are %L2B1-PENDING stubs.
;;;;
;;;; (minimize formula objective &key assumptions backend (strategy :linear-bdd)
;;;;                                  budget timeout order phase hint)
;;;;   -> (values MODEL COST OPTIMAL-P), or (values NIL NIL) when FORMULA plus
;;;;      ASSUMPTIONS is unsatisfiable (exactly two values, as in 0.1).
;;;;
;;;; ---------------------------------------------------------------- results
;;;; OBJECTIVE  A plain objective: a list of (weight . literal), weights
;;;;            non-negative integers, literals as for ASSUMPTIONS (0.1). Or a
;;;;            lexicographic objective (:lex O1 ... On), n >= 1, each Oi a
;;;;            plain objective: minimise O1, then O2 among the O1-optimal
;;;;            models, and so on. (:lex) with no level, a level that is not a
;;;;            list of conses, or a bad weight: TYPE-ERROR.
;;;; MODEL      Complete (every user variable), as in 0.1.
;;;; COST       MODEL's cost, always: an integer for a plain objective; for :lex
;;;;            a fresh list of n integers, MODEL's cost at each level in order.
;;;; OPTIMAL-P  T when the search proved COST optimal (lexicographically for
;;;;            :lex); NIL when BUDGET or TIMEOUT stopped it first. An incumbent
;;;;            of cost 0 (0 at every level) is optimal without a further call.
;;;;
;;;; ------------------------------------------------------------- strategies
;;;; STRATEGY: one of the four below, else TYPE-ERROR before any backend call.
;;;; All four return an optimum when nothing stops them; they differ in speed.
;;;; The descriptions are guidance; the tests check results, plus that
;;;; :CORE-GUIDED calls BACKEND-FINAL-CONFLICT.
;;;;   :linear-bdd        Default; the 0.1 search (%LINEAR-BDD). SAT-UNSAT
;;;;                      linear descent: after a model of cost C, add
;;;;                      "cost <= C-1" as a BDD over the objective (nodes
;;;;                      shared across rounds) and solve again.
;;;;   :linear-totalizer  The same descent, the bound on a totalizer over the
;;;;                      objective literals (a generalized totalizer for
;;;;                      weights, or each literal repeated by its weight), built
;;;;                      once and tightened with unit clauses on its outputs.
;;;;   :stratified        The distinct weights in decreasing order; stratum i
;;;;                      holds the entries with one of the i largest weights.
;;;;                      Linear descent over stratum 1, then over strata 1..2
;;;;                      from the incumbent, ..., the last round over the whole
;;;;                      objective, so the result is the global optimum.
;;;;   :core-guided       Lower-bound search (OLL / PM-style): solve with every
;;;;                      unrelaxed objective literal assumed false; on UNSAT,
;;;;                      BACKEND-FINAL-CONFLICT gives a core over those
;;;;                      assumptions (it may be shrunk, see the meter); relax
;;;;                      it (a totalizer over its literals; weights split by the
;;;;                      core's least weight) and raise the lower bound by that
;;;;                      weight. A SAT answer under the current assumptions is an
;;;;                      optimum; lower bound = incumbent cost also ends it.
;;;; Common to every strategy (tested):
;;;;   - The first backend call is BACKEND-SOLVE on the CNF as given (no bound,
;;;;     totalizer or relaxation clause added yet) under ASSUMPTIONS plus the
;;;;     HINT literals. When it succeeds, the cheapest completion of its answer
;;;;     (objective variables left unassigned take their cheaper value, as in
;;;;     0.1) is the first incumbent. When it fails with a HINT, the next call is
;;;;     under ASSUMPTIONS alone (an inconsistent hint is ignored); when it fails
;;;;     without one, MINIMIZE returns (values NIL NIL).
;;;;   - The incumbent only improves: a model replaces it only when strictly
;;;;     cheaper. MINIMIZE returns the incumbent (MODEL and its COST).
;;;;   - The CNF given is never modified; work on a copy.
;;;;
;;;; ----------------------------------------------------------- budget, time
;;;; BUDGET   NIL or a non-negative integer: the most decisions in total over
;;;;          every backend call this MINIMIZE makes (the unit of SOLVE's
;;;;          :BUDGET). TIMEOUT: NIL or a non-negative real, the most seconds of
;;;;          real time (GET-INTERNAL-REAL-TIME) for the whole call. Anything
;;;;          else: TYPE-ERROR.
;;;;          The meter (when either is given): every BACKEND-SOLVE call the
;;;;          search makes, directly or through BACKEND-FINAL-CONFLICT, gets an
;;;;          integer :BUDGET (tested). BACKEND-UNSAT-CORE takes no budget, so a
;;;;          metered search shrinks cores with its own BACKEND-SOLVE calls.
;;;;          Each call runs inside a HANDLER-BIND on SAT-BUDGET-EXCEEDED that
;;;;          counts decisions, checks the clock and lets the call go on with
;;;;          STORE-VALUE while both limits allow (conditions.lisp). The limits
;;;;          are checked before each decision and before each backend call but
;;;;          the first: once decisions >= BUDGET or elapsed >= TIMEOUT, no
;;;;          further decision is made and no further call starts. A backend
;;;;          that ignores :BUDGET is checked between calls only. The backend's
;;;;          own SAT-BUDGET-EXCEEDED never reaches the caller.
;;;;          Out of budget or time with an incumbent: (values MODEL COST NIL),
;;;;          no signal (OPTIMAL-P T only if the incumbent is known optimal).
;;;;          Out of budget or time with no model yet: SAT-BUDGET-EXCEEDED with
;;;;          BUDGET = the decision budget or TIMEOUT = the seconds, whichever
;;;;          ran out (the other slot NIL). CONTINUE doubles that limit and the
;;;;          search resumes where it stopped; USE-VALUE: MINIMIZE returns
;;;;          (values VALUE NIL); unhandled, it is an error.
;;;;          Consequence (tested): with BUDGET 0 or TIMEOUT 0, a complete HINT
;;;;          on a clause-shaped formula (the first call needs no decision)
;;;;          gives exactly the hint, its cost and OPTIMAL-P NIL (T when the
;;;;          cost is 0); without a hint the first call cannot decide, so
;;;;          SAT-BUDGET-EXCEEDED is signalled.
;;;;
;;;; ------------------------------------------------------ order, phase, hint
;;;; ORDER, PHASE  As for SOLVE (ORDER on names; PHASE NIL, :TRUE, :FALSE or a
;;;;          function on names; same checks and errors), passed to every
;;;;          BACKEND-SOLVE and BACKEND-FINAL-CONFLICT call (and so to the
;;;;          BACKEND-SOLVE inside the latter's default method). With PHASE NIL
;;;;          the default methods may pass phases of their own (the hint's
;;;;          values, then the incumbent's: solution-guided phases).
;;;; HINT     NIL, or a list whose elements are literal formulas, (name .
;;;;          boolean) conses, or atoms (bare names: the positive literal). A
;;;;          model from SOLVE or MINIMIZE is a hint; so is a partial one.
;;;;          Variables first seen in the hint are added as free user
;;;;          variables. A non-literal formula or NIL element:
;;;;          SAT-INVALID-FORMULA. Used by the first call (above).
;;;;
;;;; ---------------------------------------------------------------- :lex
;;;; Levels in order, each with STRATEGY. Once level i is proven optimal at
;;;; c_i, "level-i cost <= c_i" becomes a hard constraint and level i+1 starts
;;;; from the incumbent. BUDGET and TIMEOUT are shared by every level; running
;;;; out at level i returns the incumbent (optimal for levels < i), its cost at
;;;; every level, and OPTIMAL-P NIL. A literal may appear in several levels.
;;;;
;;;; ------------------------------------------------------- backend level
;;;; BACKEND-MINIMIZE (protocol.lisp header) receives the same arguments at
;;;; index level: OBJECTIVE over integer literals (plain or (:lex ...)), HINT
;;;; as integer literals, ORDER / PHASE as index-level hooks (as SOLVE passes
;;;; them to BACKEND-SOLVE), STRATEGY / BUDGET / TIMEOUT unchanged, and returns
;;;; (values LITERALS COST OPTIMAL-P) or (values NIL NIL). The front end checks
;;;; every argument before the call, maps LITERALS to the complete MODEL (as
;;;; 0.1) and passes COST and OPTIMAL-P through.

(in-package #:sat-protocol)

(defun %minimize (backend cnf objective &key assumptions strategy budget timeout
                                              order phase hint)
  "Default method of BACKEND-MINIMIZE for every 0.2 argument (see this file's
header): STRATEGY on BACKEND-SOLVE / BACKEND-FINAL-CONFLICT, the BUDGET /
TIMEOUT meter, HINT, and :LEX objectives."
  (declare (ignore backend cnf objective assumptions strategy budget timeout
                   order phase hint))
  (%l2b1-pending '%minimize))
