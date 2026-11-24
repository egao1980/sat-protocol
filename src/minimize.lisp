;;;; MINIMIZE 0.2 (Track L, slice L2b-1): strategies, budgets, hints and
;;;; lexicographic objectives. Specifies the front end MINIMIZE (protocol.lisp)
;;;; and the default method of BACKEND-MINIMIZE, which calls %MINIMIZE below
;;;; for every 0.2 argument. Signatures GIVEN; %MINIMIZE and the 0.2 path of
;;;; MINIMIZE (%MINIMIZE-FRONT) are implemented here (see "implementation"
;;;; after this header).
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
;;;; ---------------------------------------------------------- sessions, 0.3
;;;; SESSION-MINIMIZE (session.lisp) runs this same search, on a copy of the
;;;; session CNF (stateless) or through the session's GFs (stateful). Its one
;;;; difference: out of budget with an incumbent it SIGNALs SAT-BUDGET-REACHED
;;;; (USE-BEST, CONTINUE, STORE-VALUE) before stopping. MINIMIZE and
;;;; BACKEND-MINIMIZE are unchanged.
;;;;
;;;; ------------------------------------------------------- backend level
;;;; BACKEND-MINIMIZE (protocol.lisp header) receives the same arguments at
;;;; index level: OBJECTIVE over integer literals (plain or (:lex ...)), HINT
;;;; as integer literals, ORDER / PHASE as index-level hooks (as SOLVE passes
;;;; them to BACKEND-SOLVE), STRATEGY / BUDGET / TIMEOUT unchanged, and returns
;;;; (values LITERALS COST OPTIMAL-P) or (values NIL NIL). The front end checks
;;;; every argument before the call, maps LITERALS to the complete MODEL (as
;;;; 0.1) and passes COST and OPTIMAL-P through.
;;;;
;;;; --------------------------------------------------------- implementation
;;;; %MINIMIZE keeps one %SEARCH per call. Every backend call goes through one
;;;; gate, %CALL, which adds the caller's assumptions, the (total) ORDER /
;;;; PHASE hooks and the meter, and hands every SAT answer to %OFFER: the
;;;; answer, projected on the variables of the CNF given and completed on the
;;;; objective variables, becomes the incumbent when it is strictly cheaper
;;;; (lexicographically over the levels). So the incumbent is always a model,
;;;; whatever the strategy; a strategy only proves a level optimal.
;;;; - Levels are normalised: per variable, w.l + w'.(not l) = min(w,w') +
;;;;   |w-w'| on the dominant literal; costs are always computed from the
;;;;   entries as given.
;;;; - Strategies work on a copy of the base CNF per level (per stratum round
;;;;   for :STRATIFIED), so their bounds never leak; a proven :LEX level is
;;;;   hardened on the base with %ADD-PB (cardinality.lisp).
;;;; - Hooks: the given ORDER sees only candidates of the CNF given (the
;;;;   lowest candidate is decided when none is left) and the given PHASE only
;;;;   its variables; the search's own auxiliaries get phase NIL. With PHASE NIL
;;;;   the search passes its own phase: an objective variable's cheaper value,
;;;;   else the incumbent's value, else the hint's, else T.
;;;; - The meter steps each call's :BUDGET one decision at a time with
;;;;   STORE-VALUE; out of limits it throws to the call's stop tag (with an
;;;;   incumbent) or signals MINIMIZE's own SAT-BUDGET-EXCEEDED from inside the
;;;;   handler, so CONTINUE resumes the stopped call where it stopped.

(in-package #:sat-protocol)

(deftype %strategy ()
  "The MINIMIZE :STRATEGY values (0.2)."
  '(member :linear-bdd :linear-totalizer :stratified :core-guided))

;;; ------------------------------------------------------------- front end

(defun %map-objective (objective literal)
  "OBJECTIVE (plain, or (:lex O1 ... On) with n >= 1) checked (TYPE-ERROR for a
bad level, entry or weight), each entry's literal mapped by the function
LITERAL. A fresh objective. Shared by %INDEX-OBJECTIVE and, 0.3,
SESSION-MINIMIZE (session literals)."
  (flet ((plain (level)
           (check-type level list)
           (mapcar (lambda (entry)
                     (check-type entry cons)
                     (let ((weight (car entry)))
                       (check-type weight (integer 0 *))
                       (cons weight (funcall literal (cdr entry)))))
                   level)))
    (if (and (consp objective) (eq (first objective) :lex))
        (let ((levels (rest objective)))
          (unless (and (consp levels) (%proper-list-p levels))
            (error 'type-error :datum objective
                               :expected-type '(cons (eql :lex) (cons list list))))
          (cons :lex (mapcar #'plain levels)))
        (plain objective))))

(defun %index-objective (cnf objective)
  "OBJECTIVE (plain, or (:lex O1 ... On) with n >= 1) checked and mapped to
integer literals of CNF (TYPE-ERROR for a bad level, entry or weight)."
  (%map-objective objective (lambda (literal) (cnf-literal cnf literal))))

(defun %hint-literal (cnf element)
  "A HINT element as an integer literal of CNF: (name . boolean) gives the
variable of NAME or its negation; a literal formula or a bare name goes through
CNF-LITERAL (a non-literal formula or NIL: SAT-INVALID-FORMULA). New names
become free user variables."
  (if (consp element)
      (let ((index (cnf-ensure-variable cnf (literal-name (car element)))))
        (if (cdr element) index (- index)))
      (cnf-literal cnf element)))

(defun %minimize-front (formula objective &key assumptions backend strategy budget timeout
                                               order phase hint)
  "MINIMIZE with 0.2 arguments (protocol.lisp): every argument checked, then
one BACKEND-MINIMIZE call at index level, then the complete MODEL."
  (catch '%sat-front-value
    (check-type strategy %strategy)
    (check-type budget (or null (integer 0 *)))
    (check-type timeout (or null (real 0 *)))
    (check-type hint list)
    (let* ((backend (%resolve-backend backend formula))
           (cnf (%working-cnf formula))
           ;; Allocation order: objective, assumptions, hint.
           (ints-objective (%index-objective cnf objective))
           (ints (%integer-literals cnf assumptions))
           (ints-hint (mapcar (lambda (element) (%hint-literal cnf element)) hint))
           ;; Built now: a bad :PHASE signals SAT-ERROR before any search.
           (order-hook (and order (%order-wrapper cnf order)))
           (phase-hook (and phase (%phase-wrapper cnf phase))))
      (multiple-value-bind (literals cost optimal-p)
          (backend-minimize backend cnf ints-objective
                            :assumptions ints :strategy strategy :budget budget
                            :timeout timeout :order order-hook :phase phase-hook
                            :hint ints-hint)
        (if cost
            (values (%model cnf literals (constantly nil)) cost optimal-p)
            (values nil nil))))))

;;; ------------------------------------------------------------ the search

(defstruct (%level (:constructor %make-level (entries offset softs))
                   (:copier nil) (:predicate nil))
  entries        ; the level as given ((w . integer-literal) ...): costs come from it
  offset         ; what every model pays: sum over variables of min(P, N)
  softs)         ; ((w . literal) ...): one per variable, w > 0, first-occurrence order

(defstruct (%search (:constructor %make-search) (:conc-name %s-)
                    (:copier nil) (:predicate nil))
  backend
  base           ; private copy of the CNF given; :LEX hardening goes here
  n0             ; variable count of the CNF given: answers are projected on 1..N0
  assumptions    ; the caller's integer assumptions, part of every call
  order phase    ; total index-level hooks (PHASE never NIL)
  levels         ; list of %LEVEL
  completion     ; ((v . value) ...): every objective variable and its cheaper value
  preferences    ; v -> value, for the variables whose cheaper value is strict
  hint-table     ; v -> value of the hint (own phases)
  metered budget timeout start (used 0) (calls 0)
  best best-cost best-table           ; the incumbent: literals, cost list, v -> value
  (tag (list '%stop))                 ; fresh per call: out of limits with an incumbent
  lex                                 ; 0.3: the objective is (:lex ...): costs are lists
  budget-reached)                     ; 0.3, sessions only: SIGNAL SAT-BUDGET-REACHED first

(defun %normalize-level (entries)
  (let ((table (make-hash-table)) (vars '()) (offset 0) (softs '()))
    (loop for (weight . literal) in entries
          for v = (abs literal)
          for cell = (or (gethash v table)
                         (progn (push v vars) (setf (gethash v table) (cons 0 0))))
          do (if (plusp literal) (incf (car cell) weight) (incf (cdr cell) weight)))
    (dolist (v (nreverse vars))
      (destructuring-bind (p . n) (gethash v table)
        (incf offset (min p n))
        (cond ((> p n) (push (cons (- p n) v) softs))
              ((> n p) (push (cons (- n p) (- v)) softs)))))
    (%make-level entries offset (nreverse softs))))

(defun %lex< (a b)
  "Lexicographic < on equal-length lists of integers."
  (loop for x in a for y in b
        do (cond ((< x y) (return t))
                 ((> x y) (return nil)))
        finally (return nil)))

(defun %objective-preferences (levels)
  "Per objective variable (first occurrence), the value whose per-level cost
vector is lexicographically smaller; NIL on a tie (0.1's cheapest completion
for one level). Returns (values completion-alist strict-table)."
  (let ((vectors (make-hash-table)) (vars '()) (n (length levels)))
    (loop for level in levels
          for i from 0
          do (loop for (weight . literal) in (%level-entries level)
                   for v = (abs literal)
                   for cell = (or (gethash v vectors)
                                  (progn (push v vars)
                                         (setf (gethash v vectors)
                                               (cons (make-list n :initial-element 0)
                                                     (make-list n :initial-element 0)))))
                   do (incf (nth i (if (plusp literal) (car cell) (cdr cell))) weight)))
    (let ((completion '()) (strict (make-hash-table)))
      (dolist (v (nreverse vars))
        (destructuring-bind (if-true . if-false) (gethash v vectors)
          (let ((value (%lex< if-true if-false)))
            (push (cons v value) completion)
            (when (or value (%lex< if-false if-true))
              (setf (gethash v strict) value)))))
      (values (nreverse completion) strict))))

(defun %terms-cost (terms table)
  "Sum of the weights of TERMS ((w . integer-literal) ...) true under TABLE
(v -> value; every variable of TERMS bound)."
  (loop for (weight . literal) in terms
        when (eq (gethash (abs literal) table) (plusp literal)) sum weight))

(defun %offer (s literals)
  "A SAT answer: project it on 1..N0, give each objective variable it leaves
unassigned its cheaper value, and make it the incumbent when its cost list is
strictly smaller. Returns the completed assignment (v -> value)."
  (let ((table (make-hash-table)) (n0 (%s-n0 s)) (completed '()))
    (dolist (l literals)
      (when (<= (abs l) n0)
        (setf (gethash (abs l) table) (plusp l))
        (push l completed)))
    (loop for (v . value) in (%s-completion s)
          unless (nth-value 1 (gethash v table))
            do (setf (gethash v table) value)
               (push (if value v (- v)) completed))
    (let ((cost (mapcar (lambda (level) (%terms-cost (%level-entries level) table))
                        (%s-levels s))))
      (when (or (null (%s-best-cost s)) (%lex< cost (%s-best-cost s)))
        (setf (%s-best s) completed (%s-best-cost s) cost (%s-best-table s) table)))
    table))

;;; ------------------------------------------------------------------ hooks

(defun %total-order (order n0)
  "ORDER (index level, over the CNF given) made total over the search's own
auxiliaries (indices > N0): it sees only the candidates <= N0; when none is
left, the lowest candidate is decided."
  (and order
       (lambda (candidates)
         (let ((given (remove-if (lambda (i) (> i n0)) candidates)))
           (if given (funcall order given) (reduce #'min candidates))))))

(defun %total-phase (phase n0)
  (lambda (i) (and (<= i n0) (funcall phase i) t)))

(defun %own-phase (s)
  "PHASE NIL: an objective variable's strict cheaper value, else the
incumbent's value, else the hint's, else T; the search's auxiliaries NIL."
  (let ((n0 (%s-n0 s)))
    (lambda (i)
      (flet ((lookup (table)
               (if table (gethash i table) (values nil nil))))
        (cond ((> i n0) nil)
              (t (multiple-value-bind (value found) (lookup (%s-preferences s))
                   (if found
                       value
                       (multiple-value-bind (value found) (lookup (%s-best-table s))
                         (if found
                             value
                             (multiple-value-bind (value found) (lookup (%s-hint-table s))
                               (if found value t))))))))))))

;;; ------------------------------------------------------------------ meter

(defun %exhausted (s)
  "NIL while both limits allow one more decision or call; else :BUDGET or
:TIMEOUT."
  (let ((budget (%s-budget s)) (timeout (%s-timeout s)))
    (cond ((and budget (>= (%s-used s) budget)) :budget)
          ((and timeout (>= (- (get-internal-real-time) (%s-start s))
                            (* timeout internal-time-units-per-second)))
           :timeout))))

(defun %signal-exhausted (s which)
  "MINIMIZE's own SAT-BUDGET-EXCEEDED (no model yet), WHICH limit ran out."
  (let ((limit (if (eq which :budget) (%s-budget s) (%s-timeout s))))
    (restart-case (error 'sat-budget-exceeded
                         :budget (and (eq which :budget) limit)
                         :timeout (and (eq which :timeout) limit))
      (continue ()
        :report "Double the limit that ran out and resume the search."
        (if (eq which :budget)
            (setf (%s-budget s) (* 2 (max limit 1)))
            (setf (%s-timeout s) (max (* 2 limit) 1))))
      (use-value (value)
        :report "Stop searching; MINIMIZE returns VALUE."
        :interactive %read-value
        (%front-value value)))))

(defun %signal-reached (s)
  "0.3, SESSION-MINIMIZE's searches only (slot BUDGET-REACHED): out of budget
with an incumbent. SIGNAL SAT-BUDGET-REACHED (conditions.lisp). USE-BEST, or
SIGNAL returning, stops the search (the stop tag); CONTINUE and STORE-VALUE
raise the budget and return, so the limits are checked again and the search
resumes where it stopped."
  (let ((budget (%s-budget s)))
    ;; SIGNAL is the restartable form itself, so the restarts are associated
    ;; with the condition (CLHS 9.1.4.2.4): FIND-RESTART on it sees ours, not
    ;; the backend's CONTINUE / STORE-VALUE of its own SAT-BUDGET-EXCEEDED.
    (restart-case (signal 'sat-budget-reached
                          :budget budget
                          :cost (if (%s-lex s)
                                    (copy-list (%s-best-cost s))
                                    (first (%s-best-cost s))))
      (use-best ()
        :report "Stop the search and return the incumbent."
        (throw (%s-tag s) nil))
      (continue ()
        :report "Double the budget and resume the search."
        (setf (%s-budget s) (* 2 (max budget 1)))
        (return-from %signal-reached))
      (store-value (new-budget)
        :report "Resume the search with another budget (the most decisions of the whole call)."
        :interactive %read-budget
        (check-type new-budget (integer 0 *))
        (setf (%s-budget s) new-budget)
        (return-from %signal-reached)))
    ;; No handler took a restart: USE-BEST.
    (throw (%s-tag s) nil)))

(defun %wait-for-limits (s)
  "Return once both limits allow one more decision or call. Out of them: with
an incumbent, stop the search (0.3, a session search: SIGNAL SAT-BUDGET-REACHED
first when the budget ran out); without one, signal (CONTINUE raises the limit,
then the limits are checked again)."
  (loop for which = (%exhausted s)
        while which
        do (cond ((null (%s-best-cost s)) (%signal-exhausted s which))
                 ((and (eq which :budget) (%s-budget-reached s)) (%signal-reached s))
                 (t (throw (%s-tag s) nil)))))

(defun %call (s kind cnf extra)
  "The gate: one BACKEND-SOLVE (KIND :SOLVE) or BACKEND-FINAL-CONFLICT (KIND
:FINAL-CONFLICT) call on CNF under the caller's assumptions plus EXTRA, with
the hooks and, when metered, an integer :BUDGET stepped by the meter."
  (when (and (%s-metered s) (plusp (%s-calls s)))
    (%wait-for-limits s))                ; every call but the first
  (incf (%s-calls s))
  (let ((backend (%s-backend s))
        (assumptions (append (%s-assumptions s) extra))
        (order (%s-order s))
        (phase (%s-phase s)))
    (flet ((run (budget)
             (ecase kind
               (:solve (backend-solve backend cnf :assumptions assumptions :order order
                                                  :phase phase :budget budget))
               (:final-conflict (backend-final-conflict backend cnf assumptions :budget budget
                                                                                :order order
                                                                                :phase phase)))))
      (if (%s-metered s)
          ;; Before each decision. The handler never declines: it throws,
          ;; signals MINIMIZE's own condition (with the handlers outside this
          ;; one, CLHS 9.1.4.1) or lets the decision go on with STORE-VALUE.
          (handler-bind ((sat-budget-exceeded
                           (lambda (c)
                             (%wait-for-limits s)
                             (incf (%s-used s))
                             (store-value (1+ (sat-budget-exceeded-budget c)) c))))
            (run 0))
          (run nil)))))

(defun %solve (s cnf extra)
  "BACKEND-SOLVE through the gate: (values assignment T) for a SAT answer (the
completed assignment, see %OFFER), else (values NIL NIL)."
  (multiple-value-bind (literals sat) (%call s :solve cnf extra)
    (if sat (values (%offer s literals) t) (values nil nil))))

(defun %final-conflict (s cnf extra)
  "BACKEND-FINAL-CONFLICT through the gate: (values core T), or (values NIL NIL
assignment) for a SAT answer."
  (multiple-value-bind (core unsat literals) (%call s :final-conflict cnf extra)
    (if unsat (values core t) (values nil nil (%offer s literals)))))

;;; ------------------------------------------------------------- strategies
;;; Each takes a private WORK CNF and the level's normalised TERMS and returns
;;; once the incumbent's cost on TERMS is proven least (or, in a :STRATIFIED
;;; prefix round, once its descent ends). A cost of 0 needs no call.

(defun %descend (s work terms kind)
  "Linear SAT-UNSAT descent over TERMS from the incumbent: with R its cost on
TERMS, add \"TERMS cost <= R-1\" and solve, until UNSAT or R = 0. KIND :BDD:
the root of a BDD (nodes shared by the rounds; the propagating variant, see
%BDD-BUILDER, so the bound propagates under any :ORDER) as a unit clause. KIND :GTE: a
generalized totalizer built once, capped at the first R, tightened by a unit
clause (-o_v) for every root output v >= R. Every completion of a SAT answer
meets the bound, so R strictly decreases."
  (let ((r (%terms-cost terms (%s-best-table s)))
        (emit (lambda (clause) (cnf-add-clause work clause)))
        (bdd nil) (outputs nil) (cut nil))
    (loop
      (when (zerop r) (return))
      (ecase kind
        (:bdd
         (unless bdd (setf bdd (%bdd-builder work terms emit :propagating t)))
         (let ((root (funcall bdd (1- r))))
           (when (symbolp root) (return)) ; unreachable: 0 <= R-1 < sum of TERMS
           (cnf-add-clause work (list root))))
        (:gte
         (unless outputs (setf outputs (%gte work terms r emit) cut (1+ r)))
         (loop for (v . o) in outputs
               when (and (>= v r) (< v cut)) do (cnf-add-clause work (list (- o))))
         (setf cut r)))
      (multiple-value-bind (table sat) (%solve s work '())
        (unless sat (return))
        (setf r (%terms-cost terms table))))))

(defun %stratified (s work terms)
  "Descents over the entries of the i largest weights, i = 1, 2, ..., each on its
own copy of WORK (heuristic rounds that only improve the incumbent), then the
descent over every entry, which proves the level."
  (let ((weights (sort (remove-duplicates (mapcar #'car terms)) #'>)))
    (dolist (w (butlast weights))
      (%descend s (copy-cnf work) (remove-if (lambda (term) (< (car term) w)) terms) :bdd))
    (%descend s work terms :bdd)))

(defun %shrink (s work candidates)
  "Deletion over CANDIDATES (soft assumptions; the caller's assumptions always
stay), each test through BACKEND-FINAL-CONFLICT: a minimal sublist still
unsatisfiable with WORK. An UNSAT answer's core also drops the remaining
candidates outside it. With nothing else left an element is kept without a call
(WORK under the caller's assumptions is satisfiable: the incumbent)."
  (let ((kept '()) (rest candidates))
    (loop while rest
          do (let ((e (pop rest)))
               (if (and (null kept) (null rest))
                   (push e kept)
                   (multiple-value-bind (core unsat)
                       (%final-conflict s work (append (reverse kept) rest))
                     (if unsat
                         (setf rest (remove-if-not (lambda (x) (member x core)) rest))
                         (push e kept))))))
    (nreverse kept)))

(defun %core-guided (s work terms)
  "OLL: LOWER starts at 0 (the cost on TERMS of every model is LOWER plus the
weights left on the true exposed softs plus hidden totalizer outputs, all >= 0).
Assume every exposed soft with weight left false. SAT: that answer costs LOWER,
optimal. UNSAT: shrink the core, LOWER += its least weight W, take W off each of
its softs, and relax it with a unit totalizer whose output \">= 2\" becomes a
soft of weight W (an exposed output \">= j\" in a core exposes \">= j+1\"). Ends
when LOWER reaches the incumbent's cost; LOWER grows by >= 1 per core."
  (let ((weight (make-hash-table))      ; soft literal -> weight left
        (next (make-hash-table))        ; exposed output -> (later outputs . totalizer weight)
        (live '())                      ; soft literals, newest first
        (lower 0))
    (flet ((expose (literal w)
             (unless (nth-value 1 (gethash literal weight)) (push literal live))
             (incf (gethash literal weight 0) w))
           (goal () (%terms-cost terms (%s-best-table s))))
      (loop for (w . l) in terms do (expose l w))
      (loop
        (when (>= lower (goal)) (return))
        (let ((assume (loop for l in (reverse live)
                            when (plusp (gethash l weight)) collect (- l))))
          (multiple-value-bind (core unsat) (%final-conflict s work assume)
            (unless unsat (return))
            (let* ((softs (mapcar #'- (%shrink s work (remove-if-not (lambda (a) (member a core))
                                                                     assume))))
                   (w-min (loop for l in softs minimize (gethash l weight))))
              (unless softs
                (error 'sat-error :message "final conflict without a soft literal under a satisfiable CNF"))
              (incf lower w-min)
              (dolist (l softs)
                (decf (gethash l weight) w-min)
                (let ((later (gethash l next)))
                  (when later
                    (remhash l next)
                    (destructuring-bind (outputs . w-total) later
                      (when outputs
                        (expose (first outputs) w-total)
                        (setf (gethash (first outputs) next) (cons (rest outputs) w-total)))))))
              (when (and (rest softs) (< lower (goal)))
                ;; o_1 holds in every model (SOFTS is a core); o_2 is the new soft.
                (let ((outputs (mapcar #'cdr (%gte work (mapcar (lambda (l) (cons 1 l)) softs)
                                                   (length softs)
                                                   (lambda (clause) (cnf-add-clause work clause))))))
                  (expose (second outputs) w-min)
                  (setf (gethash (second outputs) next) (cons (cddr outputs) w-min)))))))))))

;;; ----------------------------------------------------------------- driver

(defun %first-models (s hint)
  "The first call: BACKEND-SOLVE on the CNF as given under the assumptions plus
HINT; when that fails with a HINT, once more under the assumptions alone (that
call is metered like any other). True when a model was found."
  (or (nth-value 1 (%solve s (%s-base s) hint))
      (and hint (nth-value 1 (%solve s (%s-base s) '())))))

(defun %prove-level (s level strategy)
  (let ((work (copy-cnf (%s-base s)))
        (terms (%level-softs level)))
    (ecase strategy
      (:linear-bdd (%descend s work terms :bdd))
      (:linear-totalizer (%descend s work terms :gte))
      (:stratified (%stratified s work terms))
      (:core-guided (%core-guided s work terms)))))

(defun %harden (s level)
  "A proven level becomes hard: its cost on the normalised terms stays at the
incumbent's (no big-M weights)."
  (let ((terms (%level-softs level)))
    (%add-pb (%s-base s) terms (%terms-cost terms (%s-best-table s)) :auto nil)))

(defun %minimize (backend cnf objective &key assumptions strategy budget timeout
                                              order phase hint budget-reached)
  "Default method of BACKEND-MINIMIZE for every 0.2 argument (see this file's
header): STRATEGY on BACKEND-SOLVE / BACKEND-FINAL-CONFLICT, the BUDGET /
TIMEOUT meter, HINT, and :LEX objectives. BUDGET-REACHED (0.3, private: only
the session default methods pass it): out of budget with an incumbent, SIGNAL
SAT-BUDGET-REACHED before stopping (%SIGNAL-REACHED)."
  (check-type strategy %strategy)
  (check-type budget (or null (integer 0 *)))
  (check-type timeout (or null (real 0 *)))
  (let* ((lex (and (consp objective) (eq (first objective) :lex)))
         (n0 (cnf-variable-count cnf))
         (levels (mapcar #'%normalize-level (if lex (rest objective) (list objective))))
         (s (%make-search :backend backend :base (copy-cnf cnf) :n0 n0
                          :assumptions assumptions :order (%total-order order n0)
                          :levels levels :hint-table (%assignment hint)
                          :metered (and (or budget timeout) t) :budget budget :timeout timeout
                          :start (get-internal-real-time)
                          :lex lex :budget-reached (and budget-reached t))))
    (multiple-value-bind (completion preferences) (%objective-preferences levels)
      (setf (%s-completion s) completion
            (%s-preferences s) preferences))
    (setf (%s-phase s) (if phase (%total-phase phase n0) (%own-phase s)))
    (let ((proven (catch (%s-tag s)
                    (unless (%first-models s hint)
                      (return-from %minimize (values nil nil)))
                    (loop for (level . more) on levels
                          do (%prove-level s level strategy)
                             (when more (%harden s level)))
                    t)))
      (values (copy-list (%s-best s))
              (if lex (copy-list (%s-best-cost s)) (first (%s-best-cost s)))
              proven))))
