;;;; Incremental sessions (0.3.0, Track L slice L2b-2). GIVEN: the class
;;;; SAT-SESSION, its readers SESSION-OPEN-P / SESSION-BACKEND /
;;;; SESSION-BACKEND-STATE, WITH-SAT-SESSION, the GF lambda lists, the default
;;;; methods of BACKEND-SESSION-OPEN and BACKEND-SESSION-CLOSE, the conditions
;;;; (conditions.lisp) and the rules below. IMPLEMENTED here: the front ends,
;;;; the other default methods and the session path of the strategies
;;;; (%SESSION-PROXY, at the end of this file; the SAT-BUDGET-REACHED hook is
;;;; %SIGNAL-REACHED in minimize.lisp).
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

;;; --------------------------------------------------------------- helpers

(defun %closed (session)
  "SAT-SESSION-CLOSED for an operation on the closed SESSION, signalled before
the operation does anything. USE-VALUE (value): the operation returns VALUE."
  (restart-case (error 'sat-session-closed :session session)
    (use-value (value)
      :report "Return a value from the session operation instead."
      :interactive %read-value
      value)))

(defmacro %when-open ((session &key two-values) &body body)
  "BODY's values when SESSION is open. Closed: SAT-SESSION-CLOSED first
(%CLOSED), and the operation returns the USE-VALUE value, as (values VALUE NIL)
when TWO-VALUES."
  (let ((s (gensym "SESSION")))
    `(let ((,s ,session))
       (if (%session-open ,s)
           (progn ,@body)
           ,(if two-values `(values (%closed ,s) nil) `(%closed ,s))))))

(defun %forget (session)
  "Clear the stored model and core."
  (setf (%session-model session) nil
        (%session-core session) nil))

(defun %session-literal (session literal)
  "LITERAL when it is a literal of SESSION (a non-zero integer, |LITERAL| at
most the variable count), else SAT-INVALID-FORMULA (DATUM = LITERAL)."
  (unless (and (integerp literal) (/= literal 0)
               (<= (abs literal) (cnf-variable-count (%session-cnf session))))
    (error 'sat-invalid-formula :datum literal :message "not a literal of the session"))
  literal)

(defun %session-model-of (session literals)
  "The MODEL of a backend answer LITERALS: one literal per user variable (a
named index) in index order, +i when LITERALS make it true, else -i."
  (let ((true (make-hash-table)))
    (dolist (l literals)
      (when (plusp l) (setf (gethash l true) t)))
    (loop for name across (%cnf-names (%session-cnf session))
          for i from 1
          when name collect (if (gethash i true) i (- i)))))

(defun %no-session-method (gf backend session)
  "The default method of GF met a stateful SESSION: BACKEND opened it but does
not specialise GF."
  (error 'sat-error
         :message (format nil "~S opened the stateful session ~S but has no ~S method"
                          backend session gf)))

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
    (declare (ignore clauses))
    ;; Stateless: the session CNF already holds them.
    (when (session-backend-state session)
      (%no-session-method 'backend-session-add-clauses backend session))
    nil))

(defgeneric backend-session-solve (backend session &key assumptions order phase budget)
  (:documentation "BACKEND-SOLVE over SESSION's clauses. Default (stateless):
BACKEND-SOLVE on the session's CNF.")
  (:method ((backend sat-backend) session &key assumptions order phase budget)
    (when (session-backend-state session)
      (%no-session-method 'backend-session-solve backend session))
    ;; The session's own CNF, not a copy: BACKEND-SOLVE never modifies it.
    (backend-solve backend (%session-cnf session)
                   :assumptions assumptions :order order :phase phase :budget budget)))

(defgeneric backend-session-final-conflict (backend session assumptions &key budget order phase)
  (:documentation "BACKEND-FINAL-CONFLICT over SESSION's clauses. Default
(stateless): BACKEND-FINAL-CONFLICT on the session's CNF.")
  (:method ((backend sat-backend) session assumptions &key budget order phase)
    (when (session-backend-state session)
      (%no-session-method 'backend-session-final-conflict backend session))
    (backend-final-conflict backend (%session-cnf session) assumptions
                            :budget budget :order order :phase phase)))

(defgeneric backend-session-minimize (backend session objective &key assumptions strategy budget)
  (:documentation "BACKEND-MINIMIZE over SESSION's clauses with the session
budget rule. Default: from scratch on a stateless session; through the
session's own GFs, selectors guarding every added clause, on a stateful one.")
  (:method ((backend sat-backend) session objective
            &key assumptions (strategy :linear-bdd) budget)
    (if (session-backend-state session)
        ;; Stateful: the session path (end of this file).
        (%session-path backend session objective assumptions strategy budget)
        ;; Stateless: MINIMIZE's search from scratch on the real backend.
        ;; %MINIMIZE works on its own copy and never modifies the session CNF;
        ;; never BACKEND-MINIMIZE (whose 0.1 path is not this search).
        (%minimize backend (%session-cnf session) objective
                   :assumptions assumptions :strategy strategy :budget budget
                   :budget-reached t))))

(defgeneric backend-session-close (backend session)
  (:documentation "Called once by the first CLOSE-SESSION, before SESSION is
marked closed. Default: nothing.")
  (:method ((backend sat-backend) session)
    (declare (ignore session))
    nil))

;;; ------------------------------------------------------------ front ends

(defun make-sat-session (&key backend)
  "A new open session on BACKEND (else *SAT-BACKEND*, else SAT-NO-BACKEND) with
no variable and no clause; BACKEND-SESSION-OPEN's value is its state."
  ;; USE-VALUE of SAT-NO-BACKEND throws (values VALUE NIL) here: the value only.
  (values
   (catch '%sat-front-value
     (let* ((backend (%resolve-backend backend nil))
            (session (make-instance 'sat-session :backend backend)))
       (setf (%session-state session) (backend-session-open backend session))
       session))))

(defun close-session (session)
  "T when it closed the open SESSION (BACKEND-SESSION-CLOSE first, while it is
still open), NIL when SESSION was closed already."
  (when (%session-open session)
    ;; Marked closed however the backend's close exits: it never runs twice.
    (unwind-protect (backend-session-close (session-backend session) session)
      (setf (%session-open session) nil))
    t))

(defun session-variable-count (session)
  "Every index allocated so far: user variables and auxiliaries."
  (%when-open (session)
    (cnf-variable-count (%session-cnf session))))

(defun session-cnf (session)
  "A fresh copy of the session's CNF (user variable i named i)."
  (%when-open (session)
    (copy-cnf (%session-cnf session))))

(defun session-add-variables (session count)
  "COUNT new user variables: a fresh ascending list of their indices."
  (%when-open (session)
    (check-type count (integer 0 *))
    (%forget session)
    (let ((cnf (%session-cnf session)))
      ;; Name = index; the backend reads SESSION-VARIABLE-COUNT, so no call.
      (loop repeat count
            collect (cnf-ensure-variable cnf (1+ (cnf-variable-count cnf)))))))

(defun session-add-clauses (session clauses)
  "Add CLAUSES (a list of clauses of session literals, or a FORMULA over user
variables) to SESSION; the new clauses go to BACKEND-SESSION-ADD-CLAUSES in one
call. Returns SESSION."
  (%when-open (session)
    (let* ((cnf (%session-cnf session))
           (start (cnf-clause-count cnf)))
      ;; Everything is checked before anything is added.
      (cond ((formula-p clauses)
             (dolist (name (formula-variables clauses))
               ;; Auxiliaries are unnamed: only user variables have an index.
               (unless (cnf-variable-index cnf name)
                 (error 'sat-invalid-formula :datum name
                                             :message "not a user variable of the session")))
             (%forget session)
             (to-cnf clauses :cnf cnf))
            ((listp clauses)
             (dolist (clause clauses)
               (unless (listp clause)
                 (error 'sat-invalid-formula :datum clause
                                             :message "a clause is a list of session literals"))
               (dolist (literal clause)
                 (%session-literal session literal)))
             (%forget session)
             (dolist (clause clauses)
               (cnf-add-clause cnf clause)))
            (t
             (error 'sat-invalid-formula :datum clauses
                                         :message "neither a list of clauses nor a formula")))
      ;; The new clauses by position (no full copy per add); their
      ;; auxiliaries are allocated already, so the backend sees the final count.
      (let ((new (loop with store = (%cnf-clauses cnf)
                       for p from start below (cnf-clause-count cnf)
                       collect (copy-list (aref store p)))))
        (when new
          (backend-session-add-clauses (session-backend session) session new)))
      session)))

(defun session-solve (session &key assumptions budget)
  "(values MODEL T) for the session's clauses under ASSUMPTIONS, or (values NIL
NIL) with the final conflict stored as the core. See this file's header."
  (%when-open (session :two-values t)
    (check-type assumptions list)
    (dolist (literal assumptions)
      (%session-literal session literal))
    (check-type budget (or null (integer 0 *)))
    ;; Cleared first: a USE-VALUE exit, a throw or an error leaves no answer.
    (%forget session)
    (catch '%sat-front-value
      (multiple-value-bind (core unsat literals)
          (backend-session-final-conflict (session-backend session) session assumptions
                                          :budget budget)
        (if unsat
            (progn
              (setf (%session-core session) (list (copy-list core)))
              (values nil nil))
            (let ((model (%session-model-of session literals)))
              (setf (%session-model session) (list model))
              (values (copy-list model) t)))))))

(defun session-minimize (session objective &key assumptions budget (strategy :linear-bdd))
  "(values MODEL COST OPTIMAL-P) of least COST for OBJECTIVE (session literals)
under ASSUMPTIONS, or (values NIL NIL). See this file's header."
  (%when-open (session :two-values t)
    ;; MINIMIZE's shape checks (TYPE-ERROR); literals are the session's.
    (let ((objective (%map-objective objective
                                     (lambda (literal) (%session-literal session literal)))))
      (check-type assumptions list)
      (dolist (literal assumptions)
        (%session-literal session literal))
      (check-type strategy %strategy)
      (check-type budget (or null (integer 0 *)))
      (%forget session)
      (catch '%sat-front-value
        (multiple-value-bind (literals cost optimal-p)
            (backend-session-minimize (session-backend session) session objective
                                      :assumptions assumptions :strategy strategy
                                      :budget budget)
          (if cost
              (let ((model (%session-model-of session literals)))
                (setf (%session-model session) (list model))
                (values (copy-list model) cost optimal-p))
              (progn
                ;; Unsatisfiable under ASSUMPTIONS: every assumption is a core.
                (setf (%session-core session) (list (copy-list assumptions)))
                (values nil nil))))))))

(defun session-model (session)
  "(values MODEL T): the last answer's model (a fresh copy), else (values NIL NIL)."
  (%when-open (session :two-values t)
    (let ((stored (%session-model session)))
      (if stored
          (values (copy-list (first stored)) t)
          (values nil nil)))))

(defun session-unsat-core (session &key minimal)
  "(values CORE T) after an UNSAT answer, else (values NIL NIL). MINIMAL: the
stored core is first made minimal (%MINIMAL-CORE), and replaces it."
  (%when-open (session :two-values t)
    (let ((stored (%session-core session)))
      (cond ((null stored) (values nil nil))
            (t
             (when minimal
               (setf (%session-core session)
                     (list (%minimal-core session (first stored)))))
             (values (copy-list (first (%session-core session))) t))))))

(defun %minimal-core (session core)
  "Deletion with clause-set refinement over CORE (this file's header): one
BACKEND-SESSION-FINAL-CONFLICT per test under KEPT ++ REST, no budget. On a
stateless session (every final conflict is every assumption) this is
BACKEND-UNSAT-CORE's deletion, element for element."
  (let ((backend (session-backend session))
        (kept '())
        (rest core))
    (loop while rest
          do (let ((e (pop rest)))
               (multiple-value-bind (conflict unsat)
                   (backend-session-final-conflict backend session (revappend kept rest))
                 (if unsat
                     (setf rest (remove-if-not (lambda (x) (member x conflict)) rest))
                     (push e kept)))))
    (nreverse kept)))

;;; ------------------------------------------------------ the session path
;;; The stateful default of BACKEND-SESSION-MINIMIZE. %MINIMIZE runs unchanged
;;; over %SESSION-PROXY, a private SAT-BACKEND: each work CNF %MINIMIZE hands it
;;; (the base copy of the session CNF, the per-level copies, the :STRATIFIED
;;; round copies) is a VIEW with its own SELECTOR.
;;; - Positions < K0 of every work CNF are the session's own clauses, already
;;;   in the backend unguarded; variables 1..N0 are the session's (identity).
;;; - A work CNF's later clauses go to BACKEND-SESSION-ADD-CLAUSES once each,
;;;   as (-SELECTOR . clause), its variables > N0 renumbered to fresh unnamed
;;;   session auxiliaries (allocated before the push). The selector is
;;;   allocated when the view first has a clause to push, and recorded for
;;;   retirement before anything it guards is pushed.
;;; - A call on a view assumes its selector, the negation of every other
;;;   selector of the call (exact activation: other views' clauses are
;;;   satisfied before the search, so the budget meters this view's search
;;;   only), then the work assumptions translated. Answers and cores come back
;;;   through the inverse map; selectors and other views' auxiliaries drop out.
;;;   Sound both ways: a model of the work CNF extends to the backend's clauses
;;;   with this selector true and every other one false.
;;; - However %MINIMIZE exits (a return, USE-BEST, a throw from a
;;;   SAT-BUDGET-REACHED handler, a USE-VALUE exit, an error), the cleanup
;;;   pushes the unit (-SELECTOR) of every selector of the call in one call.
;;;   The session CNF never gains a clause, only unnamed auxiliaries.

(defclass %session-proxy (sat-backend)
  ((backend :initarg :backend :reader %proxy-backend
            :documentation "The session's real backend.")
   (session :initarg :session :reader %proxy-session)
   (k0 :initarg :k0 :reader %proxy-k0
       :documentation "The session's clause count when the call started.")
   (n0 :initarg :n0 :reader %proxy-n0
       :documentation "The session's variable count when the call started.")
   (views :initform '() :accessor %proxy-views
          :documentation "((work-cnf . %VIEW) ...), newest first; EQ lookup only.")
   (selectors :initform '() :accessor %proxy-selectors
              :documentation "Every selector of the call, newest first."))
  (:documentation "The session path's private backend: %MINIMIZE's calls on its
work CNFs become session GF calls on the real backend (see above)."))

(defstruct (%view (:constructor %make-view (pushed mapped))
                  (:copier nil) (:predicate nil))
  pushed     ; the work CNF's clauses [0, PUSHED) hold in the backend (from K0: guarded)
  mapped     ; the work CNF's variables 1..MAPPED have session indices
  selector   ; NIL until the work CNF first has a clause to push
  (forward (make-array 0 :adjustable t :fill-pointer 0)) ; work N0+1+k -> session index
  (inverse (make-hash-table)))                           ; session index -> work index

(defun %to-session (proxy view literal)
  "Work LITERAL -> session literal: the identity on 1..N0, else VIEW's auxiliary."
  (let ((v (abs literal)) (n0 (%proxy-n0 proxy)))
    (if (<= v n0)
        literal
        (let ((i (aref (%view-forward view) (- v n0 1))))
          (if (plusp literal) i (- i))))))

(defun %to-work (proxy view literal)
  "Session LITERAL -> work literal of VIEW, or NIL (a selector, another view's
auxiliary)."
  (let ((v (abs literal)))
    (if (<= v (%proxy-n0 proxy))
        literal
        (let ((j (gethash v (%view-inverse view))))
          (and j (if (plusp literal) j (- j)))))))

(defun %to-work-literals (proxy view literals)
  (loop for l in literals
        for w = (%to-work proxy view l)
        when w collect w))

(defun %sync (proxy cnf)
  "The view of work CNF, its new variables mapped to fresh session auxiliaries
and its new clauses pushed (one call), guarded by its selector."
  (let* ((session (%proxy-session proxy))
         (scnf (%session-cnf session))
         (view (or (cdr (assoc cnf (%proxy-views proxy) :test #'eq))
                   (let ((view (%make-view (%proxy-k0 proxy) (%proxy-n0 proxy))))
                     (push (cons cnf view) (%proxy-views proxy))
                     view))))
    ;; Variables first, ascending: every pushed literal is a session variable.
    (loop for j from (1+ (%view-mapped view)) to (cnf-variable-count cnf)
          do (let ((i (cnf-ensure-variable scnf nil)))
               (vector-push-extend i (%view-forward view))
               (setf (gethash i (%view-inverse view)) j
                     (%view-mapped view) j)))
    (let ((count (cnf-clause-count cnf)))
      (when (< (%view-pushed view) count)
        (unless (%view-selector view)
          (let ((selector (cnf-ensure-variable scnf nil)))
            ;; Recorded first: retired even if the push below is cut short.
            (push selector (%proxy-selectors proxy))
            (setf (%view-selector view) selector)))
        (let ((guard (- (%view-selector view)))
              (store (%cnf-clauses cnf)))
          (backend-session-add-clauses
           (%proxy-backend proxy) session
           (loop for p from (%view-pushed view) below count
                 collect (cons guard (mapcar (lambda (l) (%to-session proxy view l))
                                             (aref store p)))))
          (setf (%view-pushed view) count))))
    view))

(defun %view-assumptions (proxy view assumptions)
  "A call's session assumptions: VIEW's selector, every other selector of the
call negated (allocation order), then the work ASSUMPTIONS translated."
  (let ((own (%view-selector view)))
    (nconc (and own (list own))
           (loop for selector in (reverse (%proxy-selectors proxy))
                 unless (eql selector own) collect (- selector))
           (mapcar (lambda (l) (%to-session proxy view l)) assumptions))))

(defun %view-phase (proxy view phase)
  "PHASE (work indices) on session indices; an index outside VIEW gets NIL."
  (and phase
       (lambda (i)
         (let ((j (%to-work proxy view i)))
           (and j (funcall phase j) t)))))

(defun %view-order (proxy view order)
  "ORDER (work indices) on session candidates: it sees those of VIEW; when none
is left, the lowest candidate is decided."
  (and order
       (lambda (candidates)
         (let ((mapped (loop for i in candidates
                             for j = (%to-work proxy view i)
                             when j collect j)))
           (if mapped
               (%to-session proxy view (funcall order (sort mapped #'<)))
               (reduce #'min candidates))))))

(defmethod backend-solve ((proxy %session-proxy) cnf &key assumptions order phase budget)
  (let ((view (%sync proxy cnf)))
    (multiple-value-bind (literals sat)
        (backend-session-solve (%proxy-backend proxy) (%proxy-session proxy)
                               :assumptions (%view-assumptions proxy view assumptions)
                               :order (%view-order proxy view order)
                               :phase (%view-phase proxy view phase)
                               ;; Unchanged: the meter sees the backend's signal.
                               :budget budget)
      (if sat
          (values (%to-work-literals proxy view literals) t)
          (values nil nil)))))

(defmethod backend-final-conflict ((proxy %session-proxy) cnf assumptions
                                   &key budget order phase)
  (let ((view (%sync proxy cnf)))
    (multiple-value-bind (core unsat literals)
        (backend-session-final-conflict (%proxy-backend proxy) (%proxy-session proxy)
                                        (%view-assumptions proxy view assumptions)
                                        :budget budget
                                        :order (%view-order proxy view order)
                                        :phase (%view-phase proxy view phase))
      (if unsat
          ;; Selector literals dropped: a sublist of ASSUMPTIONS, given order.
          (values (%to-work-literals proxy view core) t)
          (values nil nil (%to-work-literals proxy view literals))))))

(defun %retire (proxy)
  "Unit clauses (-selector) for every selector of the call, in allocation
order, in one BACKEND-SESSION-ADD-CLAUSES call (none when there is none, or
when a handler closed the session during the call)."
  (let ((selectors (reverse (%proxy-selectors proxy)))
        (session (%proxy-session proxy)))
    (setf (%proxy-selectors proxy) '())
    (when (and selectors (%session-open session))
      (backend-session-add-clauses (%proxy-backend proxy) session
                                   (mapcar (lambda (selector) (list (- selector))) selectors)))))

(defun %session-path (backend session objective assumptions strategy budget)
  "The stateful default of BACKEND-SESSION-MINIMIZE: %MINIMIZE over a
%SESSION-PROXY of SESSION, every selector retired however it exits."
  (let* ((cnf (%session-cnf session))
         ;; %MINIMIZE copies CNF and reads its counts on entry, before the
         ;; proxy allocates any auxiliary in it.
         (proxy (make-instance '%session-proxy
                               :backend backend :session session
                               :k0 (cnf-clause-count cnf) :n0 (cnf-variable-count cnf))))
    (unwind-protect
         (%minimize proxy cnf objective
                    :assumptions assumptions :strategy strategy :budget budget
                    :budget-reached t)
      (%retire proxy))))
