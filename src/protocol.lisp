;;;; Backends and front ends. Specials, classes and GF lambda lists are GIVEN;
;;;; the default methods and the front ends are implemented here.
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
;;;; (backend-minimize backend cnf objective &key assumptions strategy budget
;;;;                   timeout order phase hint)                    ; 0.2 keys
;;;;   OBJECTIVE: list of (weight . integer-literal), or (0.2) (:lex O1 ... On)
;;;;   of such lists. -> (values LITERALS COST OPTIMAL-P) for a model of least
;;;;   COST (sum of the weights of its true literals; a list of per-level costs
;;;;   for :lex), or (values NIL NIL) when unsatisfiable. OPTIMAL-P (0.2) is NIL
;;;;   when BUDGET / TIMEOUT stopped the search first. ORDER / PHASE are index
;;;;   level (as BACKEND-SOLVE), HINT is a list of integer literals; STRATEGY,
;;;;   BUDGET, TIMEOUT: see minimize.lisp, which specifies the default method
;;;;   (%MINIMIZE). The front end has checked every argument. With the 0.1
;;;;   arguments only (STRATEGY :LINEAR-BDD, the rest NIL, a plain objective) the
;;;;   default method is the 0.1 linear descent and returns OPTIMAL-P T.
;;;;   0.2 adds keys to the GF lambda list: a 0.1 method that accepts only
;;;;   :ASSUMPTIONS is no longer congruent (CLHS 7.6.4); no published backend
;;;;   specialises BACKEND-MINIMIZE.
;;;; (backend-unsat-core backend cnf assumptions)
;;;;   -> (values CORE T) with CORE a subset of the integer literals ASSUMPTIONS
;;;;   (kept in their given order) such that CNF plus CORE is unsatisfiable and
;;;;   removing any one element of CORE makes it satisfiable; or (values NIL NIL)
;;;;   when CNF plus ASSUMPTIONS is satisfiable.
;;;; (backend-final-conflict backend cnf assumptions &key budget order phase)
;;;;                                                                    ; 0.2
;;;;   BACKEND-SOLVE under ASSUMPTIONS, explaining UNSAT with a cheap core.
;;;;   UNSAT -> (values CORE T), CORE a sublist of the integer literals
;;;;   ASSUMPTIONS (given order) such that CNF plus CORE is unsatisfiable (any
;;;;   sublist when CNF alone is), not necessarily minimal. Satisfiable ->
;;;;   (values NIL NIL LITERALS), LITERALS as BACKEND-SOLVE returns them. CNF is
;;;;   not modified. BUDGET, ORDER, PHASE as for BACKEND-SOLVE. Default method:
;;;;   one BACKEND-SOLVE call with these arguments; UNSAT -> a fresh copy of
;;;;   ASSUMPTIONS (all of them). A backend with assumption-based conflict
;;;;   analysis (CDCL) returns the final conflict of that call instead.
;;;;   :CORE-GUIDED and UNSAT-CORE :MINIMAL NIL use it.
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
;;;; (minimize formula objective &key assumptions backend strategy budget
;;;;           timeout order phase hint) -> (values MODEL COST OPTIMAL-P)
;;;;   OBJECTIVE: list of (weight . literal), weights non-negative integers (else
;;;;   TYPE-ERROR). MODEL is complete and of least COST = sum of weights of its
;;;;   true objective literals. Unsatisfiable -> (values NIL NIL). This is the
;;;;   weighted-preference API: "prefer x" is (1 . (sat-not x)).
;;;;   0.2: the third value OPTIMAL-P, the keys STRATEGY (default :LINEAR-BDD,
;;;;   the 0.1 behaviour), BUDGET, TIMEOUT, ORDER, PHASE, HINT and
;;;;   lexicographic objectives (:lex O1 ... On): specified in minimize.lisp.
;;;;   With the 0.1 arguments the result is the 0.1 result plus OPTIMAL-P T;
;;;;   unsatisfiable is still exactly (values NIL NIL).
;;;;
;;;; (unsat-core formula &key assumptions named backend (minimal t))
;;;;   -> (values CORE T) or (values NIL NIL) when FORMULA plus every assumption
;;;;   and every named formula is satisfiable. NAMED: alist (name . formula), soft
;;;;   like ASSUMPTIONS. FORMULA is hard. CORE lists the ASSUMPTIONS elements (EQ,
;;;;   given order) and then the NAMED names (given order) of a minimal
;;;;   unsatisfiable subset: FORMULA plus CORE is unsatisfiable, and dropping any
;;;;   one element makes it satisfiable. FORMULA alone unsatisfiable ->
;;;;   (values NIL T).
;;;;   0.2, MINIMAL NIL: the same mapping over BACKEND-FINAL-CONFLICT instead of
;;;;   BACKEND-UNSAT-CORE: FORMULA plus CORE is unsatisfiable, CORE need not be
;;;;   minimal (when FORMULA alone is unsatisfiable it may be any subset).

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
    ;; Each BACKEND-SOLVE answer is a partial assignment P satisfying every
    ;; clause, so every completion of P is a model. The answer's assigned
    ;; projected literals form a cube; its completions over the unassigned
    ;; projected indices are enumerated lazily (an odometer), then the cube is
    ;; blocked. Cubes are pairwise contradictory, so no model repeats.
    (let ((work (copy-cnf cnf))
          (project (remove-duplicates project :from-end t))
          (cube #())        ; parallel to PROJECT: the answer's literal, or NIL
          (next 0)          ; odometer over the NIL entries of CUBE
          (end 0)
          (last nil)        ; the cube was empty: it covered every model
          (done nil))
      (lambda ()
        (loop
          (cond ((< next end)
                 (let ((bits next) (j -1))
                   (incf next)
                   (return (values (loop for i in project
                                         for l across cube
                                         collect (or l (if (logbitp (incf j) bits) i (- i))))
                                   t))))
                ((or done last)
                 (setf done t)
                 (return (values nil nil)))
                (t
                 (multiple-value-bind (literals sat)
                     (backend-solve backend work :assumptions assumptions)
                   (if (not sat)
                       (setf done t)
                       (let ((assigned (make-hash-table)))
                         (dolist (l literals) (setf (gethash (abs l) assigned) l))
                         (setf cube (map 'vector (lambda (i) (values (gethash i assigned))) project)
                               next 0
                               end (ash 1 (count nil cube)))
                         (let ((block (loop for l across cube when l collect (- l))))
                           (if block
                               (cnf-add-clause work block)
                               (setf last t)))))))))))))

(defun %cheapest-completion (literals objective)
  "LITERALS plus, for each objective variable they leave unassigned, its
cheaper value. Returns (values literals cost)."
  (let ((assigned (make-hash-table))
        (preference (make-hash-table))   ; variable -> cost(T) - cost(F)
        (order '()))
    (dolist (l literals) (setf (gethash (abs l) assigned) (plusp l)))
    (loop for (weight . l) in objective
          for v = (abs l)
          unless (nth-value 1 (gethash v assigned))
            do (unless (nth-value 1 (gethash v preference)) (push v order))
               (incf (gethash v preference 0) (if (plusp l) weight (- weight))))
    (let ((completed (copy-list literals)))
      (dolist (v (nreverse order))
        (let ((value (minusp (gethash v preference))))
          (setf (gethash v assigned) value)
          (push (if value v (- v)) completed)))
      (values completed
              (loop for (weight . l) in objective
                    when (eq (gethash (abs l) assigned) (plusp l)) sum weight)))))

(defun %linear-bdd (backend cnf objective assumptions)
  "The 0.1 default method (GIVEN, unchanged but for the third value):
unbudgeted linear descent with a BDD bound over a plain integer OBJECTIVE.
Returns (values literals cost T), or (values NIL NIL). 0.2's :LINEAR-BDD
strategy (minimize.lisp) may reuse or replace it; with the 0.1 arguments its
results must not change."
  ;; Linear SAT-UNSAT descent. After a model of cost C, assert
  ;; "cost <= C-1" with a BDD over the objective entries: node N(i,k) means
  ;; "entries i.. weigh at most k when true", clauses (-N -l_i N(i+1,k-w_i))
  ;; and (-N l_i N(i+1,k)). The node table is shared by every tightening.
  ;; The bound is clauses, so every completion of a partial answer meets it,
  ;; and the cheapest completion strictly lowers the cost each round.
  (let* ((work (copy-cnf cnf))
         (terms (coerce objective 'vector))
         (n (length terms))
         (suffix (make-array (1+ n) :initial-element 0))
         (memo (make-hash-table :test 'equal))
         (best-literals nil)
         (best nil))
    (loop for i from (1- n) downto 0
          do (setf (aref suffix i) (+ (aref suffix (1+ i)) (car (aref terms i)))))
    (labels ((node (i k)
               (cond ((minusp k) :false)
                     ((>= k (aref suffix i)) :true)
                     (t (let ((key (cons i k)))
                          (or (gethash key memo)
                              (setf (gethash key memo)
                                    (destructuring-bind (weight . l) (aref terms i)
                                      ;; children first (post-order allocation)
                                      (let* ((hi (node (1+ i) (- k weight)))
                                             (lo (node (1+ i) k))
                                             (x (cnf-ensure-variable work nil)))
                                        (flet ((imply (lit child)
                                                 (unless (eq child :true)
                                                   (cnf-add-clause work (if (eq child :false)
                                                                            (list (- x) lit)
                                                                            (list (- x) lit child))))))
                                          (imply (- l) hi)
                                          (imply l lo))
                                        x)))))))))
      (loop
        (multiple-value-bind (literals sat)
            (backend-solve backend work :assumptions assumptions)
          (unless sat (return))
          (multiple-value-setq (best-literals best) (%cheapest-completion literals objective))
          (when (zerop best) (return))
          (let ((root (node 0 (1- best))))
            (when (symbolp root) (return)) ; unreachable for 0 < best <= sum of weights
            (cnf-add-clause work (list root))))))
    (if best
        (values best-literals best t)
        (values nil nil))))

(defgeneric backend-minimize (backend cnf objective
                                      &key assumptions strategy budget timeout order phase hint)
  (:documentation "Least-cost model. Default method: the strategies of
minimize.lisp on BACKEND-SOLVE / BACKEND-FINAL-CONFLICT; with the 0.1 arguments
only, the 0.1 linear descent (%LINEAR-BDD).")
  (:method ((backend sat-backend) cnf objective
            &key assumptions (strategy :linear-bdd) budget timeout order phase hint)
    (if (and (eq strategy :linear-bdd)
             (null budget) (null timeout) (null order) (null phase) (null hint)
             (not (eq (first objective) :lex)))
        (%linear-bdd backend cnf objective assumptions)
        (%minimize backend cnf objective
                   :assumptions assumptions :strategy strategy :budget budget
                   :timeout timeout :order order :phase phase :hint hint))))

(defgeneric backend-unsat-core (backend cnf assumptions)
  (:documentation "Minimal unsatisfiable subset of ASSUMPTIONS. Default method: deletion.")
  (:method ((backend sat-backend) cnf assumptions)
    ;; Deletion: drop each element whose removal keeps the rest UNSAT.
    ;; Invariant: KEPT ++ REST is UNSAT; a kept element was necessary against
    ;; a superset of the final core, hence also against the core (monotone).
    (flet ((sat-p (subset)
             (nth-value 1 (backend-solve backend cnf :assumptions subset))))
      (if (sat-p assumptions)
          (values nil nil)
          (let ((kept '()))
            (loop for tail on assumptions
                  when (sat-p (revappend kept (rest tail)))
                    do (push (first tail) kept))
            (values (nreverse kept) t))))))

(defgeneric backend-final-conflict (backend cnf assumptions &key budget order phase)
  (:documentation "0.2: BACKEND-SOLVE under ASSUMPTIONS that also explains an
UNSAT answer with a cheap core (a sublist of ASSUMPTIONS, not necessarily
minimal). Default method: one BACKEND-SOLVE call; UNSAT -> all of ASSUMPTIONS.
See the header of protocol.lisp.")
  (:method ((backend sat-backend) cnf assumptions &key budget order phase)
    (declare (ignore cnf assumptions budget order phase))
    (%l2b1-pending 'backend-final-conflict)))

;;; ------------------------------------------------------------ front ends

(defun %working-cnf (formula)
  "A private CNF for FORMULA (the caller's object is never modified)."
  (if (cnf-p formula)
      (copy-cnf formula)
      (to-cnf (%check-formula formula))))

(defun %integer-literals (cnf literals)
  (mapcar (lambda (l) (cnf-literal cnf l)) literals))

(defun %assignment (literals)
  "Hash table index -> T / NIL."
  (let ((table (make-hash-table)))
    (dolist (l literals table)
      (setf (gethash (abs l) table) (plusp l)))))

(defun %model (cnf literals fill)
  "User variables in index order. Unassigned ones are bound to (FILL name)
when FILL is a function, else left out."
  (let ((assignment (%assignment literals)))
    (loop for i from 1 to (cnf-variable-count cnf)
          for name = (cnf-variable-name cnf i)
          when name
            if (nth-value 1 (gethash i assignment))
              collect (cons name (gethash i assignment))
            else if fill
                   collect (cons name (and (funcall fill name) t)))))

(defun %order-wrapper (cnf order)
  "ORDER on names -> the index-level hook BACKEND-SOLVE calls."
  (lambda (candidates)
    (let ((user (remove-if (lambda (i) (cnf-aux-variable-p cnf i)) candidates)))
      (if (null user)
          (reduce #'min candidates)
          (let* ((user (sort (copy-list user) #'<))
                 (names (mapcar (lambda (i) (cnf-variable-name cnf i)) user))
                 (choice (funcall order names))
                 (position (position choice names :test #'equal)))
            (if position
                (nth position user)
                (error 'sat-error
                       :message (format nil ":ORDER returned ~S, not one of ~S" choice names))))))))

(defun %phase-wrapper (cnf phase)
  "PHASE (:TRUE, :FALSE or a function on names) -> a function on indices."
  (cond ((eq phase :true) (constantly t))
        ((eq phase :false) (constantly nil))
        ((functionp phase)
         (lambda (i)
           (let ((name (cnf-variable-name cnf i)))
             (if name (and (funcall phase name) t) t))))
        (t (error 'sat-error
                  :message (format nil ":PHASE must be NIL, :TRUE, :FALSE or a function, not ~S"
                                   phase)))))

(defun %fill-function (phase)
  (cond ((eq phase :true) (constantly t))
        ((functionp phase) phase)
        (t (constantly nil))))

(defun solve (formula &key assumptions order phase budget backend (complete t))
  (catch '%sat-front-value
    (let* ((backend (%resolve-backend backend formula))
           (cnf (%working-cnf formula))
           (ints (%integer-literals cnf assumptions))
           (order-hook (and order (%order-wrapper cnf order)))
           (phase-hook (and phase (%phase-wrapper cnf phase))))
      (multiple-value-bind (literals sat)
          (backend-solve backend cnf :assumptions ints :order order-hook
                                     :phase phase-hook :budget budget)
        (if sat
            (values (%model cnf literals (and complete (%fill-function phase))) t)
            (values nil nil))))))

(defun solve-all (formula &key project limit assumptions backend)
  (catch '%sat-front-value
    (let* ((backend (%resolve-backend backend formula))
           (cnf (%working-cnf formula))
           (ints (%integer-literals cnf assumptions))
           (indices (if project
                        (remove-duplicates (mapcar (lambda (p) (abs (cnf-literal cnf p))) project)
                                           :from-end t)
                        (loop for i from 1 to (cnf-variable-count cnf)
                              unless (cnf-aux-variable-p cnf i) collect i)))
           (generator nil)
           (count 0))
      (make-instance
       'model-sequence
       :generator (lambda ()
                    (if (and limit (>= count limit))
                        (values nil nil)
                        (progn
                          ;; Created on the first NEXT-MODEL: :LIMIT 0 never searches.
                          (unless generator
                            (setf generator (backend-solve-all backend cnf :project indices
                                                                           :assumptions ints)))
                          (multiple-value-bind (literals ok) (funcall generator)
                            (if ok
                                (let ((assignment (%assignment literals)))
                                  (incf count)
                                  (values (mapcar (lambda (i)
                                                    (cons (cnf-variable-name cnf i)
                                                          (gethash i assignment)))
                                                  indices)
                                          t))
                                (values nil nil))))))))))

(defun minimize (formula objective &key assumptions backend (strategy :linear-bdd)
                         budget timeout order phase hint)
  ;; 0.2 arguments: minimize.lisp. The 0.1 path below is GIVEN.
  (when (or (not (eq strategy :linear-bdd)) budget timeout order phase hint
            (and (consp objective) (eq (first objective) :lex)))
    (return-from minimize (%l2b1-pending 'minimize)))
  (catch '%sat-front-value
    (let* ((backend (%resolve-backend backend formula))
           (cnf (%working-cnf formula))
           (ints-objective
            (mapcar (lambda (entry)
                      (check-type entry cons)
                      (let ((weight (car entry)))
                        (check-type weight (integer 0 *))
                        (cons weight (cnf-literal cnf (cdr entry)))))
                    objective))
           (ints (%integer-literals cnf assumptions)))
      (multiple-value-bind (literals cost optimal-p)
          (backend-minimize backend cnf ints-objective :assumptions ints)
        (if cost
            (values (%model cnf literals (constantly nil)) cost optimal-p)
            (values nil nil))))))

(defun unsat-core (formula &key assumptions named backend (minimal t))
  (catch '%sat-front-value
    (let* ((backend (%resolve-backend backend formula))
           (cnf (%working-cnf formula))
           (ints (%integer-literals cnf assumptions))
           (selectors
            (loop for (nil . soft) in named
                  collect (let ((soft (%check-formula soft)))
                            (dolist (name (formula-variables soft))
                              (cnf-ensure-variable cnf name))
                            ;; An auxiliary selector S with clauses S -> SOFT.
                            (let ((s (cnf-ensure-variable cnf nil)))
                              (%add-formula cnf soft s)
                              s))))
           (all (append ints selectors))
           (objects (append assumptions (mapcar #'car named))))
      (multiple-value-bind (core unsat)
          (if minimal
              (backend-unsat-core backend cnf all)
              (backend-final-conflict backend cnf all)) ; 0.2
        (if unsat
            ;; By position: CORE is a subsequence of ALL, so walk both.
            (values (loop for i in all
                          for object in objects
                          when (and core (eql i (first core)))
                            collect object
                            and do (pop core))
                    t)
            (values nil nil))))))
