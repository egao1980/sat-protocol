;;;; Backends and front ends. Specials, classes and GF lambda lists are GIVEN;
;;;; the default methods and the front ends are stubs.
;;;;
;;;; ---------------------------------------------------------------- backends
;;;; A backend is an instance of a SAT-BACKEND subclass. It must implement
;;;; BACKEND-SOLVE. BACKEND-SOLVE-ALL, BACKEND-MINIMIZE and BACKEND-UNSAT-CORE
;;;; have default methods here built on BACKEND-SOLVE (blocking clauses,
;;;; iterated solving with a tightened bound, deletion over assumptions); a
;;;; backend may specialise them.
;;;;
;;;; (backend-solve backend cnf &key assumptions order phase budget)
;;;;   CNF is not modified. ASSUMPTIONS: integer literals that must hold.
;;;;   Returns (values LITERALS T): the integer literals the search assigned
;;;;   (assumptions, decisions and implied literals, each variable at most once),
;;;;   such that every clause contains one of them; or (values NIL NIL) when the
;;;;   CNF is unsatisfiable under ASSUMPTIONS.
;;;;   The search stops as soon as every clause has a true literal: it does not
;;;;   assign variables it does not need.
;;;;   ORDER: NIL, or a function of one argument, CANDIDATES (the ascending list
;;;;   of indices of unassigned variables that occur in a clause with no true
;;;;   literal), returning one of them. When ORDER is given the backend calls it
;;;;   for every decision and decides exactly that variable, and makes no other
;;;;   choice (no pure-literal elimination); it may still assign literals
;;;;   implied by the clauses (unit propagation). With ORDER NIL the backend
;;;;   chooses freely.
;;;;   PHASE: NIL (backend's choice), or a function index -> boolean: the value
;;;;   tried first when deciding that variable.
;;;;   BUDGET: NIL, or a non-negative integer: the most decisions the search may
;;;;   make. Before the decision that would exceed it, the backend calls
;;;;   (SIGNAL-BUDGET-EXCEEDED budget) and continues with the returned budget.
;;;;
;;;; (backend-solve-all backend cnf &key project assumptions)
;;;;   -> a function of no arguments returning (values LITERALS T) per projected
;;;;   model, then (values NIL NIL). PROJECT: list of indices; LITERALS assign
;;;;   exactly those indices; each distinct projected model comes exactly once.
;;;; (backend-minimize backend cnf objective &key assumptions)
;;;;   OBJECTIVE: list of (weight . integer-literal). -> (values LITERALS COST)
;;;;   for a model of least COST (sum of the weights of its true literals), or
;;;;   (values NIL NIL) when unsatisfiable.
;;;; (backend-unsat-core backend cnf assumptions)
;;;;   -> (values CORE T) with CORE a subset of the integer literals ASSUMPTIONS
;;;;   (kept in their given order) such that CNF plus CORE is unsatisfiable and
;;;;   removing any one element of CORE makes it satisfiable; or (values NIL NIL)
;;;;   when CNF plus ASSUMPTIONS is satisfiable.
;;;;
;;;; -------------------------------------------------------------- front ends
;;;; FORMULA is a FORMULA or a CNF (never modified). Literals are literal
;;;; formulas or bare names. :BACKEND overrides *SAT-BACKEND*; with neither,
;;;; SAT-NO-BACKEND (see conditions.lisp). Each front end catches
;;;; '%SAT-FRONT-VALUE (USE-VALUE of SAT-NO-BACKEND / SAT-BUDGET-EXCEEDED).
;;;; Variables first seen in assumptions, a projection or an objective are added
;;;; to a copy of the CNF as free user variables.
;;;;
;;;; (solve formula &key assumptions order phase budget backend (complete t))
;;;;   -> (values MODEL T), or (values NIL NIL) when unsatisfiable (under the
;;;;   assumptions). A satisfiable formula with nothing to bind gives (values NIL T).
;;;;   ORDER: NIL, or a function (names) -> one of NAMES. It is called for each
;;;;   decision with the candidate user variables (unassigned, in a clause with no
;;;;   true literal) in CNF index order, and the search decides the name it
;;;;   returns. Auxiliaries never reach the hook: when only auxiliary candidates
;;;;   remain, the lowest auxiliary index is decided. A result that is not one of
;;;;   NAMES signals SAT-ERROR.
;;;;   PHASE: NIL (backend's choice), :TRUE, :FALSE, or a function name -> boolean
;;;;   (auxiliaries: backend's choice).
;;;;   BUDGET: NIL or a non-negative integer, passed to the backend.
;;;;   COMPLETE T: MODEL binds every user variable; variables the search left
;;;;   unassigned get the phase value (:TRUE -> T, a function -> its value,
;;;;   otherwise NIL). COMPLETE NIL: MODEL binds exactly the user variables the
;;;;   search assigned; the formula holds whatever the others are.
;;;;
;;;; (solve-all formula &key project limit assumptions backend) -> MODEL-SEQUENCE
;;;;   Every distinct model projected on PROJECT (default: all user variables),
;;;;   each exactly once, in any order; each model binds exactly the PROJECT
;;;;   variables, in PROJECT order (default: CNF index order). LIMIT: at most that
;;;;   many models. SAT-NO-BACKEND is signalled by SOLVE-ALL itself (USE-VALUE:
;;;;   SOLVE-ALL returns the value).
;;;;
;;;; (minimize formula objective &key assumptions backend) -> (values MODEL COST)
;;;;   OBJECTIVE: list of (weight . literal), weights non-negative integers (else
;;;;   TYPE-ERROR). MODEL is complete and of least COST = sum of weights of its
;;;;   true objective literals. Unsatisfiable -> (values NIL NIL). This is the
;;;;   weighted-preference API: "prefer x" is (1 . (sat-not x)).
;;;;
;;;; (unsat-core formula &key assumptions named backend) -> (values CORE T) or
;;;;   (values NIL NIL) when FORMULA plus every assumption and every named formula
;;;;   is satisfiable. NAMED: alist (name . formula), soft like ASSUMPTIONS.
;;;;   FORMULA is hard. CORE lists the ASSUMPTIONS elements (EQ, given order) and
;;;;   then the NAMED names (given order) of a minimal unsatisfiable subset:
;;;;   FORMULA plus CORE is unsatisfiable, and dropping any one element makes it
;;;;   satisfiable. FORMULA alone unsatisfiable -> (values NIL T).

(in-package #:sat-protocol)

(defvar *sat-backend* nil
  "Default SAT backend for the front ends; a SAT-BACKEND instance or NIL.")

(defclass sat-backend () ()
  (:documentation "Root class of SAT backends. Subclasses implement BACKEND-SOLVE."))

(defgeneric backend-solve (backend cnf &key assumptions order phase budget)
  (:documentation "Search CNF. See the header of protocol.lisp."))

(defgeneric backend-solve-all (backend cnf &key project assumptions)
  (:documentation "Generator of projected models. Default method: blocking clauses.")
  (:method ((backend sat-backend) cnf &key project assumptions)
    (declare (ignore cnf project assumptions))
    (%sat-pending 'backend-solve-all)))

(defgeneric backend-minimize (backend cnf objective &key assumptions)
  (:documentation "Least-cost model. Default method: iterated BACKEND-SOLVE with a tightened bound.")
  (:method ((backend sat-backend) cnf objective &key assumptions)
    (declare (ignore cnf objective assumptions))
    (%sat-pending 'backend-minimize)))

(defgeneric backend-unsat-core (backend cnf assumptions)
  (:documentation "Minimal unsatisfiable subset of ASSUMPTIONS. Default method: deletion.")
  (:method ((backend sat-backend) cnf assumptions)
    (declare (ignore cnf assumptions))
    (%sat-pending 'backend-unsat-core)))

(defun solve (formula &key assumptions order phase budget backend (complete t))
  (declare (ignore formula assumptions order phase budget backend complete))
  (%sat-pending 'solve))

(defun solve-all (formula &key project limit assumptions backend)
  (declare (ignore formula project limit assumptions backend))
  (%sat-pending 'solve-all))

(defun minimize (formula objective &key assumptions backend)
  (declare (ignore formula objective assumptions backend))
  (%sat-pending 'minimize))

(defun unsat-core (formula &key assumptions named backend)
  (declare (ignore formula assumptions named backend))
  (%sat-pending 'unsat-core))
