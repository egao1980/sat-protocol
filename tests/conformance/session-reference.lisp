;;;; 0.3 (L2b-2) session helpers. GIVEN test code, no stubs.
;;;;
;;;; REFERENCE-SESSION-BACKEND: REFERENCE-BACKEND with a native, stateful
;;;; session. Its state is every clause the protocol passed to
;;;; BACKEND-SESSION-ADD-CLAUSES (in order); each session call runs
;;;; REFERENCE-SEARCH over them. It learns nothing, so its answers depend only
;;;; on what the protocol pushed: it is the oracle for the protocol's session
;;;; path (stateful SESSION-MINIMIZE: selectors, guarded bounds, retirement)
;;;; without a real incremental solver. Its final conflict is every assumption,
;;;; as the default BACKEND-FINAL-CONFLICT.
;;;;
;;;; Plus the shared helpers of session-test.lisp: sessions built from clause
;;;; lists or a CNF, model and core checks, and brute force over a session's
;;;; user variables.

(in-package #:sat-protocol/conformance)

(defstruct (reference-session-state (:conc-name rss-) (:copier nil))
  (clauses (make-array 16 :adjustable t :fill-pointer 0))   ; every clause pushed
  (pushes '())                                              ; newest first: one list per call
  (calls 0)                                                 ; session searches run
  (closed nil))

(defclass reference-session-backend (reference-backend) ()
  (:default-initargs :propagate t)
  (:documentation "REFERENCE-BACKEND with a stateful session: the clauses the
protocol pushed, searched from scratch on every session call (no learning)."))

(defun %rss (session)
  (let ((state (session-backend-state session)))
    (assert (reference-session-state-p state) () "not a reference session: ~S" session)
    (assert (not (rss-closed state)) () "the reference session state is closed")
    state))

(defmethod backend-session-open ((backend reference-session-backend) session)
  (declare (ignore session))
  (make-reference-session-state))

(defmethod backend-session-add-clauses ((backend reference-session-backend) session clauses)
  (let ((state (%rss session))
        (n (session-variable-count session)))
    (dolist (c clauses)
      (dolist (l c)
        (assert (and (integerp l) (<= 1 (abs l) n)) ()
                "pushed literal ~S is not a variable of the session (1..~D)" l n))
      (vector-push-extend (copy-list c) (rss-clauses state)))
    (push (mapcar #'copy-list clauses) (rss-pushes state))
    nil))

(defun %rss-search (backend session assumptions order phase budget)
  (let ((state (%rss session))
        (n (session-variable-count session)))
    (dolist (l assumptions)
      (assert (and (integerp l) (<= 1 (abs l) n)) ()
              "assumption ~S is not a variable of the session (1..~D)" l n))
    (incf (rss-calls state))
    (reference-search (coerce (rss-clauses state) 'list)
                      :assumptions assumptions :order order :phase phase :budget budget
                      :propagate (reference-backend-propagate backend))))

(defmethod backend-session-solve ((backend reference-session-backend) session
                                  &key assumptions order phase budget)
  (%rss-search backend session assumptions order phase budget))

(defmethod backend-session-final-conflict ((backend reference-session-backend) session assumptions
                                           &key budget order phase)
  (multiple-value-bind (literals sat) (%rss-search backend session assumptions order phase budget)
    (if sat
        (values nil nil literals)
        (values (copy-list assumptions) t))))

(defmethod backend-session-close ((backend reference-session-backend) session)
  (setf (rss-closed (session-backend-state session)) t)
  nil)

(defun reference-session-clauses (session)
  "Every clause pushed to SESSION's reference state, in order (fresh lists)."
  (map 'list #'copy-list (rss-clauses (session-backend-state session))))

(defun reference-session-calls (session)
  "The number of session searches SESSION's reference state ran."
  (rss-calls (session-backend-state session)))

;;; ------------------------------------------------------------- helpers

(defun session-from-clauses (clauses nvars &rest make-args)
  "A new session (MAKE-ARGS as MAKE-SAT-SESSION) with NVARS user variables 1..NVARS
and CLAUSES."
  (let ((s (apply #'make-sat-session make-args)))
    (session-add-variables s nvars)
    (when clauses (session-add-clauses s clauses))
    s))

(defun session-from-cnf (cnf &rest make-args)
  "A new session whose variables are CNF's indices (each a user variable) and
whose clauses are CNF's: CNF's integer literals are the session's."
  (apply #'session-from-clauses (cnf-clauses cnf) (cnf-variable-count cnf) make-args))

(defun index-objective (cnf objective)
  "A name-level OBJECTIVE ((w . literal-formula-or-name) ...) over CNF's literals,
or (:lex ...) of such lists."
  (flet ((plain (level)
           (mapcar (lambda (e) (cons (car e) (cnf-literal cnf (cdr e)))) level)))
    (if (and (consp objective) (eq (first objective) :lex))
        (cons :lex (mapcar #'plain (rest objective)))
        (plain objective))))

(defun literals->names (cnf literals)
  "A model of CNF's names from integer LITERALS (CNF's indices)."
  (loop for l in literals
        for name = (cnf-variable-name cnf (abs l))
        when name collect (cons name (plusp l))))

(defun literal-true-p (literal model)
  "LITERAL (integer) under MODEL (a list of integer literals)."
  (and (member literal model) t))

(defun model-shape-ok-p (model user-vars)
  "MODEL is one literal per element of USER-VARS (ascending), in that order."
  (and (listp model)
       (= (length model) (length user-vars))
       (every (lambda (l v) (and (integerp l) (= (abs l) v))) model user-vars)))

(defun model-satisfies-p (model clauses &optional assumptions)
  "Every clause of CLAUSES has a literal of MODEL, and MODEL holds every assumption."
  (and (every (lambda (c) (some (lambda (l) (literal-true-p l model)) c)) clauses)
       (every (lambda (a) (literal-true-p a model)) assumptions)))

(defun compactor (vars)
  "A function renumbering a literal over the variables VARS to 1..|VARS| (VARS order)."
  (let ((map (make-hash-table)))
    (loop for v in vars for i from 1 do (setf (gethash v map) i))
    (lambda (l)
      (let ((i (gethash (abs l) map)))
        (assert i () "literal ~S outside ~S" l vars)
        (if (plusp l) i (- i))))))

(defun compact-clauses (clauses vars)
  "CLAUSES over the variables VARS renumbered 1..|VARS| (in VARS order)."
  (let ((f (compactor vars)))
    (mapcar (lambda (c) (mapcar f c)) clauses)))

(defun brute-sat-over-p (clauses vars &optional assumptions)
  "CLAUSES plus the unit ASSUMPTIONS satisfiable over the variables VARS."
  (brute-satisfiable-p (compact-clauses (append clauses (mapcar #'list assumptions)) vars)
                       (length vars)))

(defun brute-optimum-over (clauses vars objective &optional assumptions)
  "Least cost of OBJECTIVE (integer, or (:lex ...)) over the models of CLAUSES
plus ASSUMPTIONS on VARS, or NIL."
  (let* ((f (compactor vars))
         (lex (and (consp objective) (eq (first objective) :lex)))
         (levels (mapcar (lambda (level)
                           (mapcar (lambda (e) (cons (car e) (funcall f (cdr e)))) level))
                         (if lex (rest objective) (list objective))))
         (best (brute-lex-optimum (compact-clauses (append clauses (mapcar #'list assumptions)) vars)
                                  (length vars) levels)))
    (if lex best (first best))))

(defun model-cost (objective model)
  "OBJECTIVE's cost under MODEL (integer literals): an integer, or a list for :lex."
  (flet ((plain (level)
           (loop for (w . l) in level when (literal-true-p l model) sum w)))
    (if (and (consp objective) (eq (first objective) :lex))
        (mapcar #'plain (rest objective))
        (plain objective))))

(defun core-ok-p (core assumptions clauses vars)
  "CORE is a subsequence of ASSUMPTIONS and CLAUSES plus CORE is unsatisfiable on VARS."
  (and (subsequence-p core assumptions)
       (not (brute-sat-over-p clauses vars core))))

(defun core-minimal-p (core clauses vars)
  "Dropping any one element of CORE makes CLAUSES plus CORE satisfiable on VARS."
  (loop for i below (length core)
        always (brute-sat-over-p clauses vars
                                 (append (subseq core 0 i) (subseq core (1+ i))))))

(defun fresh-solve-status (session assumptions)
  "The status of the fresh front-end SOLVE on (SESSION-CNF SESSION)."
  (nth-value 1 (solve (session-cnf session) :assumptions (mapcar #'lit-formula assumptions))))

(defun fresh-minimize (session objective assumptions strategy)
  "(list model cost optimal-p) of the fresh front-end MINIMIZE on (SESSION-CNF SESSION)."
  (let ((name-objective
          (if (and (consp objective) (eq (first objective) :lex))
              (cons :lex (mapcar #'int-objective->literals (rest objective)))
              (int-objective->literals objective))))
    (multiple-value-list
     (minimize (session-cnf session) name-objective
               :assumptions (mapcar #'lit-formula assumptions) :strategy strategy))))

;;; Every session check (session-test.lisp) is a function of no arguments that
;;; runs on *SAT-BACKEND*; DEFINE-SESSION-CHECK also defines its DEFTEST. A
;;; backend suite can run them all on another backend with RUN-SESSION-CHECKS.

(defvar *session-checks* '()
  "Names of the session checks, in definition order.")

(defmacro define-session-check (name &body body)
  "Define the check function NAME and a DEFTEST of the same name running it."
  `(progn
     (defun ,name () ,@body)
     (unless (member ',name *session-checks*)
       (setf *session-checks* (append *session-checks* (list ',name))))
     (deftest ,name (,name))))

(defun run-session-checks (backend)
  "Run every session check with *SAT-BACKEND* bound to BACKEND, each in a
TESTING context named after it (call inside a DEFTEST)."
  (let ((*sat-backend* backend))
    (dolist (check *session-checks*)
      (testing (string-downcase (symbol-name check))
        (funcall check)))))
