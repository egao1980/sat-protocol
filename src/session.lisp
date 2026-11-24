;;;; Incremental sessions (0.3.0, Track L slice L2b-2). GIVEN: the class
;;;; SAT-SESSION, its readers SESSION-OPEN-P / SESSION-BACKEND /
;;;; SESSION-BACKEND-STATE, WITH-SAT-SESSION, the GF lambda lists, the default
;;;; methods of BACKEND-SESSION-OPEN and BACKEND-SESSION-CLOSE, the conditions
;;;; (conditions.lisp) and the rules below. STUBBED (%SESSION-PENDING): the
;;;; front ends, the other default methods and the session path of the
;;;; strategies. Add files to the .asd as needed; the rules do not depend on the
;;;; file layout.
;;;;
;;;; A session is one growing set of clauses over one backend, solved and
;;;; minimised many times under per-call assumptions. It works at index level,
;;;; like the backend GFs: variables are integers 1..N, literals are +i / -i.
;;;;
;;;; ------------------------------------------------------------ the session
;;;; (make-sat-session &key backend) -> an open session with no variable and no
;;;;   clause. BACKEND, else *SAT-BACKEND*, else SAT-NO-BACKEND (USE-BACKEND:
;;;;   retry with that backend; USE-VALUE: MAKE-SAT-SESSION returns the value).
;;;;   Then (BACKEND-SESSION-OPEN backend session), exactly once; its value is
;;;;   (SESSION-BACKEND-STATE session).
;;;; (with-sat-session (var &rest make-args) &body body): VAR is bound to
;;;;   (apply #'make-sat-session make-args); BODY's values are returned; the
;;;;   session is closed when BODY exits, normally or not.
;;;; (close-session session) -> T when it closed an open session, NIL when it
;;;;   was closed already. The first call runs (BACKEND-SESSION-CLOSE backend
;;;;   session) while the session is still open, then marks it closed.
;;;; (session-open-p s) (session-backend s) (session-backend-state s): readers;
;;;;   these three and CLOSE-SESSION never signal SAT-SESSION-CLOSED. Every
;;;;   other operation on a closed session signals it first (conditions.lisp).
;;;;
;;;; Variables. (session-add-variables session count) -> a fresh list of COUNT
;;;;   new indices, ascending and consecutive from the current count + 1. Each
;;;;   is a user variable whose name (in SESSION-CNF) is its own index. COUNT: a
;;;;   non-negative integer, else TYPE-ERROR. (session-variable-count session):
;;;;   every index allocated so far, user variables and auxiliaries (formula
;;;;   encodings, and the session path of SESSION-MINIMIZE, below).
;;;;   A LITERAL of the session is a non-zero integer L with |L| <= the count.
;;;;   An assumption, objective or clause literal that is not one signals
;;;;   SAT-INVALID-FORMULA (DATUM = that object) before anything else happens.
;;;;
;;;; Clauses only grow. (session-add-clauses session clauses) -> SESSION.
;;;;   CLAUSES is either
;;;;   - a list of clauses, each a list of literals of the session (repeats and
;;;;     complementary pairs allowed; NIL, the empty clause, makes the session
;;;;     unsatisfiable for good); or
;;;;   - a FORMULA (cardinality constraints included) whose variable names
;;;;     (FORMULA-VARIABLES) are all user variables of the session. It is
;;;;     encoded onto the session's CNF as TO-CNF with :CNF does: fresh
;;;;     auxiliaries, the clauses of to-cnf's rules.
;;;;   Anything else, a clause that is not a list, a bad literal, or a formula
;;;;   variable that is not a user variable: SAT-INVALID-FORMULA (DATUM = that
;;;;   object). Everything is checked first: on a signal nothing is added.
;;;;   The new clauses, as a fresh list of integer lists in order, then go to
;;;;   (BACKEND-SESSION-ADD-CLAUSES backend session clauses) in one call (no call
;;;;   when there are none).
;;;; (session-cnf session) -> a fresh copy (COPY-CNF) of the session's CNF:
;;;;   every variable (user variable i named i; auxiliaries unnamed) and every
;;;;   clause added, formula encodings included, in order. It never holds the
;;;;   clauses of SESSION-MINIMIZE's own encodings.
;;;;
;;;; ------------------------------------------------------------------ calls
;;;; Assumptions hold for one call only. A MODEL is a fresh list of literals,
;;;; one per user variable in index order (+i true, -i false): the backend's
;;;; answer completed with false for the user variables it left unassigned.
;;;; Every call's answer equals the answer of the fresh front-end call on
;;;; (SESSION-CNF session) at that moment, with the same assumptions (as
;;;; literal formulas): the same status, the same cost and OPTIMAL-P, and a
;;;; model of every clause so far and of the assumptions. That is the property
;;;; the tests check. On a stateless session (below) the answer of SESSION-SOLVE
;;;; is exactly SOLVE's (same backend, same model).
;;;;
;;;; (session-solve session &key assumptions budget) -> (values MODEL T), or
;;;;   (values NIL NIL) when the clauses plus ASSUMPTIONS are unsatisfiable.
;;;;   One search: (BACKEND-SESSION-FINAL-CONFLICT backend session assumptions
;;;;   :budget budget), so an UNSAT answer has its core.
;;;;   BUDGET: NIL or a non-negative integer (else TYPE-ERROR), the decisions of
;;;;   this call, as SOLVE's :BUDGET. The backend's SAT-BUDGET-EXCEEDED reaches
;;;;   the caller: CONTINUE and STORE-VALUE resume the search, USE-VALUE makes
;;;;   SESSION-SOLVE return (values VALUE NIL).
;;;;
;;;; (session-minimize session objective &key assumptions budget
;;;;                   (strategy :linear-bdd))
;;;;   -> (values MODEL COST OPTIMAL-P), or (values NIL NIL) when unsatisfiable.
;;;;   OBJECTIVE: a list of (weight . literal), or (:lex O1 ... On) of such
;;;;   lists, as MINIMIZE's but over literals of the session; COST an integer,
;;;;   or a fresh list for :lex. Shapes, weights and STRATEGY are checked as
;;;;   MINIMIZE checks them (TYPE-ERROR). The search is MINIMIZE's (minimize.lisp:
;;;;   strategies, first call, incumbent, :lex), through
;;;;   (BACKEND-SESSION-MINIMIZE backend session objective :assumptions
;;;;   :strategy :budget). Unbudgeted, COST and OPTIMAL-P (T) are MINIMIZE's on
;;;;   SESSION-CNF.
;;;;   BUDGET: NIL or a non-negative integer (else TYPE-ERROR): the decisions of
;;;;   every backend call of this call, metered as MINIMIZE's :BUDGET (checked
;;;;   before each decision and before each backend call but the first).
;;;;   - Out of budget with no model yet: SAT-BUDGET-EXCEEDED, as MINIMIZE
;;;;     (CONTINUE doubles the budget and resumes; USE-VALUE returns (values
;;;;     VALUE NIL); unhandled, an error).
;;;;   - Out of budget with an incumbent: SIGNAL SAT-BUDGET-REACHED (BUDGET, the
;;;;     incumbent's COST) with the restarts USE-BEST, CONTINUE and STORE-VALUE
;;;;     (conditions.lisp). USE-BEST, or no handler taking a restart, returns
;;;;     (values MODEL COST NIL) for the incumbent: MINIMIZE's anytime answer.
;;;;     CONTINUE and STORE-VALUE resume the search where it stopped; it may
;;;;     reach the new budget and signal again. A search that ends without
;;;;     running out (an incumbent of cost 0 needs no call) never signals.
;;;;
;;;; (session-model session) -> (values MODEL T): the model the last
;;;;   SESSION-SOLVE or SESSION-MINIMIZE returned (a fresh copy); else (values
;;;;   NIL NIL).
;;;; (session-unsat-core session &key minimal) -> (values CORE T) when the last
;;;;   SESSION-SOLVE or SESSION-MINIMIZE answered UNSAT; else (values NIL NIL).
;;;;   CORE is a fresh subsequence of that call's ASSUMPTIONS (given order) such
;;;;   that the clauses plus CORE are unsatisfiable (any subsequence, NIL
;;;;   included, when the clauses alone are). After SESSION-SOLVE it is that
;;;;   search's final conflict (the stateless default: every assumption); after
;;;;   SESSION-MINIMIZE, some core (the stateless default: every assumption).
;;;;   MINIMAL T: the stored core is first made minimal (dropping any one
;;;;   element makes it satisfiable) by deletion with clause-set refinement:
;;;;     KEPT = (), REST = the core; while REST: pop E; one
;;;;     BACKEND-SESSION-FINAL-CONFLICT call under KEPT ++ REST (no budget):
;;;;     UNSAT with core C -> drop E, REST = the elements of REST in C (EQL);
;;;;     satisfiable -> push E on KEPT. The result is KEPT in the given order;
;;;;   it replaces the stored core. So on a stateless session (whose final
;;;;   conflicts are every assumption) it is UNSAT-CORE's deletion result.
;;;;   SESSION-UNSAT-CORE never changes SESSION-MODEL.
;;;; Both are cleared ((values NIL NIL)) by SESSION-ADD-CLAUSES,
;;;; SESSION-ADD-VARIABLES, and a call that ends without an answer (a USE-VALUE
;;;; exit, a throw, an error). After such an exit the session stays usable: the
;;;; next call's answer obeys the rules above.
;;;;
;;;; ---------------------------------------------------------- backend GFs
;;;; Index level; the front ends have checked every argument and the session is
;;;; open. A backend with no native session keeps every default method.
;;;;
;;;; (backend-session-open backend session) -> STATE. Default: NIL, a STATELESS
;;;;   session: every call re-solves the session CNF from scratch with the
;;;;   backend's ordinary GFs (correct, slow), so every backend has sessions.
;;;;   Any other value makes the session STATEFUL: the backend keeps its own
;;;;   solver state (SESSION-BACKEND-STATE) and specialises
;;;;   BACKEND-SESSION-ADD-CLAUSES, -SOLVE and -FINAL-CONFLICT; their default
;;;;   methods signal SAT-ERROR on a stateful session.
;;;; (backend-session-add-clauses backend session clauses)
;;;;   CLAUSES: integer clauses the session's answers must now satisfy, over
;;;;   1..(SESSION-VARIABLE-COUNT session) (the variables are allocated first;
;;;;   new variables may also arrive with no clause, e.g. for assumptions).
;;;;   From SESSION-ADD-CLAUSES, and on a stateful session from the session
;;;;   path of SESSION-MINIMIZE. Default: nothing (stateless: the session CNF
;;;;   holds them).
;;;; (backend-session-solve backend session &key assumptions order phase budget)
;;;; (backend-session-final-conflict backend session assumptions
;;;;                                 &key budget order phase)
;;;;   BACKEND-SOLVE and BACKEND-FINAL-CONFLICT (protocol.lisp: values, hooks,
;;;;   budget, cores) over every clause the session has given the backend.
;;;;   Defaults (stateless): those GFs on the session's own CNF (not a copy;
;;;;   they never modify it).
;;;;   A stateful backend may keep anything implied by the clauses it was given
;;;;   (learnt clauses, level-0 facts, activities, phases) from one call to the
;;;;   next: since clauses only grow, that is sound. Its answers obey the rules
;;;;   of BACKEND-SOLVE / BACKEND-FINAL-CONFLICT for those clauses; any call may
;;;;   be cut short by a non-local exit (a budget USE-VALUE, a throw from a
;;;;   handler) and the next call must still be right.
;;;; (backend-session-minimize backend session objective
;;;;                           &key assumptions strategy budget)
;;;;   -> (values LITERALS COST OPTIMAL-P) or (values NIL NIL), as
;;;;   BACKEND-MINIMIZE, with the session BUDGET rule above. Default method:
;;;;   - stateless: MINIMIZE's search (%MINIMIZE) on a fresh copy of the
;;;;     session CNF through BACKEND-SOLVE / BACKEND-FINAL-CONFLICT, from
;;;;     scratch. The session CNF gains nothing.
;;;;   - stateful (the session path): the same search with every backend call
;;;;     through BACKEND-SESSION-SOLVE / BACKEND-SESSION-FINAL-CONFLICT on this
;;;;     session (never BACKEND-SOLVE, BACKEND-FINAL-CONFLICT or
;;;;     BACKEND-MINIMIZE), so what the backend learns serves every later call.
;;;;     Bounds and relaxations must not outlive the call: every clause the
;;;;     search adds (bounds, totalizers, relaxations, :lex hardening) goes to
;;;;     BACKEND-SESSION-ADD-CLAUSES with the negation of a SELECTOR variable,
;;;;     and the calls that need those clauses assume the selector. Selectors
;;;;     and the search's other variables are fresh auxiliaries of the session
;;;;     CNF (with no clause there). Before SESSION-MINIMIZE returns, by any
;;;;     means, each selector of the call gets a unit clause (-selector) through
;;;;     BACKEND-SESSION-ADD-CLAUSES, so every clause the call added is
;;;;     satisfied for good, and later answers are those of the clauses added
;;;;     with SESSION-ADD-CLAUSES alone.
;;;;     A way to get there (guidance, not tested): run %MINIMIZE unchanged over
;;;;     a private SAT-BACKEND whose BACKEND-SOLVE / BACKEND-FINAL-CONFLICT map
;;;;     each work CNF (a copy of the session CNF plus the strategy's clauses) to
;;;;     a selector: push the clauses the work CNF gained since the last call,
;;;;     guarded, with its auxiliaries renumbered to fresh session auxiliaries;
;;;;     translate assumptions, hooks, answers and cores both ways.
;;;; (backend-session-close backend session): release the state. Default:
;;;;   nothing.
;;;;
;;;; Call counts the tests check: BACKEND-SESSION-OPEN once per session;
;;;; BACKEND-SESSION-CLOSE once; BACKEND-SESSION-ADD-CLAUSES once per
;;;; SESSION-ADD-CLAUSES that adds a clause, with exactly those clauses;
;;;; BACKEND-SESSION-FINAL-CONFLICT once per SESSION-SOLVE (assumptions as
;;;; given, ORDER and PHASE NIL); BACKEND-SESSION-MINIMIZE once per
;;;; SESSION-MINIMIZE (the index-level objective as given, strategy, budget).

(in-package #:sat-protocol)

(defun %session-pending (name)
  "Contract stub for sat-protocol 0.3.0 (Track L, slice L2b-2). Every call is
replaced by the implementation, then this function is deleted. Signals a
SIMPLE-ERROR (deliberately not a SAT-ERROR, so no negative test passes on a
stub)."
  (error "sat-protocol 0.3 (L2b-2) pending: ~S" name))

;;; ------------------------------------------------------------- the class

(defclass sat-session ()
  ((backend :initarg :backend :reader session-backend
            :documentation "The backend every call of the session uses.")
   (state :initform nil :accessor %session-state :reader session-backend-state
          :documentation "BACKEND-SESSION-OPEN's value: NIL for a stateless session.")
   (cnf :initform (make-cnf) :reader %session-cnf
        :documentation "Every variable and clause added; user variable i is named i.")
   (open :initform t :accessor %session-open
         :documentation "NIL once CLOSE-SESSION ran.")
   (model :initform nil :accessor %session-model
          :documentation "NIL, or a one-element list: the stored model.")
   (core :initform nil :accessor %session-core
         :documentation "NIL, or a one-element list: the stored core."))
  (:documentation "An incremental SAT session: clauses that only grow, solved
and minimised under per-call assumptions. See session.lisp."))

(defmethod print-object ((s sat-session) stream)
  (print-unreadable-object (s stream :type t :identity t)
    (format stream "~:[closed~;~D var~:P, ~D clause~:P~]" (%session-open s)
            (cnf-variable-count (%session-cnf s)) (cnf-clause-count (%session-cnf s)))))

(defun session-open-p (session)
  "True until CLOSE-SESSION ran on SESSION."
  (and (%session-open session) t))

(defmacro with-sat-session ((var &rest make-args) &body body)
  "Bind VAR to a new session (MAKE-SAT-SESSION with MAKE-ARGS) around BODY and
close it however BODY exits."
  `(let ((,var (make-sat-session ,@make-args)))
     (unwind-protect (progn ,@body)
       (close-session ,var))))

;;; ---------------------------------------------------------- backend GFs

(defgeneric backend-session-open (backend session)
  (:documentation "Called once by MAKE-SAT-SESSION. Returns the backend's state
for SESSION; NIL (the default) makes a stateless session.")
  (:method ((backend sat-backend) session)
    (declare (ignore session))
    nil))

(defgeneric backend-session-add-clauses (backend session clauses)
  (:documentation "CLAUSES (integer lists) now hold in SESSION. Default:
nothing for a stateless session; SAT-ERROR for a stateful one.")
  (:method ((backend sat-backend) session clauses)
    (declare (ignore session clauses))
    (%session-pending 'backend-session-add-clauses)))

(defgeneric backend-session-solve (backend session &key assumptions order phase budget)
  (:documentation "BACKEND-SOLVE over SESSION's clauses. Default (stateless):
BACKEND-SOLVE on the session's CNF.")
  (:method ((backend sat-backend) session &key assumptions order phase budget)
    (declare (ignore session assumptions order phase budget))
    (%session-pending 'backend-session-solve)))

(defgeneric backend-session-final-conflict (backend session assumptions &key budget order phase)
  (:documentation "BACKEND-FINAL-CONFLICT over SESSION's clauses. Default
(stateless): BACKEND-FINAL-CONFLICT on the session's CNF.")
  (:method ((backend sat-backend) session assumptions &key budget order phase)
    (declare (ignore session assumptions budget order phase))
    (%session-pending 'backend-session-final-conflict)))

(defgeneric backend-session-minimize (backend session objective &key assumptions strategy budget)
  (:documentation "BACKEND-MINIMIZE over SESSION's clauses with the session
budget rule. Default: from scratch on a stateless session; through the
session's own GFs, selectors guarding every added clause, on a stateful one.")
  (:method ((backend sat-backend) session objective &key assumptions strategy budget)
    (declare (ignore session objective assumptions strategy budget))
    (%session-pending 'backend-session-minimize)))

(defgeneric backend-session-close (backend session)
  (:documentation "Called once by the first CLOSE-SESSION, before SESSION is
marked closed. Default: nothing.")
  (:method ((backend sat-backend) session)
    (declare (ignore session))
    nil))

;;; ------------------------------------------------------------ front ends

(defun make-sat-session (&key backend)
  (declare (ignore backend))
  (%session-pending 'make-sat-session))

(defun close-session (session)
  (declare (ignore session))
  (%session-pending 'close-session))

(defun session-variable-count (session)
  (declare (ignore session))
  (%session-pending 'session-variable-count))

(defun session-cnf (session)
  (declare (ignore session))
  (%session-pending 'session-cnf))

(defun session-add-variables (session count)
  (declare (ignore session count))
  (%session-pending 'session-add-variables))

(defun session-add-clauses (session clauses)
  (declare (ignore session clauses))
  (%session-pending 'session-add-clauses))

(defun session-solve (session &key assumptions budget)
  (declare (ignore session assumptions budget))
  (%session-pending 'session-solve))

(defun session-minimize (session objective &key assumptions budget (strategy :linear-bdd))
  (declare (ignore session objective assumptions budget strategy))
  (%session-pending 'session-minimize))

(defun session-model (session)
  (declare (ignore session))
  (%session-pending 'session-model))

(defun session-unsat-core (session &key minimal)
  (declare (ignore session minimal))
  (%session-pending 'session-unsat-core))
