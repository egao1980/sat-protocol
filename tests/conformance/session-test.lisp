(in-package #:sat-protocol/conformance)

;;; 0.3 (L2b-2) incremental sessions on *SAT-BACKEND* (session.lisp's rules).
;;; The key property: every session call answers as the fresh front-end call on
;;; (SESSION-CNF session) with the same assumptions, checked against brute force
;;; over the session's user variables (at most 9 per random session) and against
;;; that fresh call. Each check is a DEFINE-SESSION-CHECK, so sat-protocol/tests
;;; also runs them on REFERENCE-SESSION-BACKEND (a stateful session).
;;; The budget checks assume a deterministic backend: the same calls on a fresh
;;; session give the same answers.

;;; --------------------------------------------------------------- scripts

(defun random-clause* (rng vars width)
  "A clause of WIDTH distinct variables of VARS (all of them when fewer), random signs."
  (let ((chosen '()))
    (loop while (< (length chosen) (min width (length vars)))
          do (pushnew (nth (rng-int rng (length vars)) vars) chosen))
    (mapcar (lambda (v) (if (zerop (rng-int rng 2)) v (- v))) chosen)))

(defun random-literals* (rng vars k)
  "K random literals over VARS (repeats and complementary pairs allowed)."
  (loop repeat k
        collect (let ((v (nth (rng-int rng (length vars)) vars)))
                  (if (zerop (rng-int rng 2)) v (- v)))))

(defun random-objective* (rng vars nterms)
  "NTERMS entries (w . literal), weights 1..3, literals over VARS."
  (loop repeat nterms collect (cons (1+ (rng-int rng 3)) (first (random-literals* rng vars 1)))))

(defun objective-literals (objective)
  (remove-duplicates (mapcar #'cdr (if (and (consp objective) (eq (first objective) :lex))
                                       (apply #'append (rest objective))
                                       objective))))

(defun check-solve-step (s vars clauses assumptions label)
  "One SESSION-SOLVE: the status against brute force and the fresh SOLVE; on SAT
the model and SESSION-MODEL; on UNSAT the final conflict and the minimal core.
Returns the status."
  (multiple-value-bind (model sat) (session-solve s :assumptions assumptions)
    (ok (eq (brute-sat-over-p clauses vars assumptions) sat) (format nil "~A: status" label))
    (ok (eq sat (fresh-solve-status s assumptions)) (format nil "~A: the fresh SOLVE's status" label))
    (if sat
        (progn
          (ok (and (model-shape-ok-p model vars) (model-satisfies-p model clauses assumptions))
              (format nil "~A: a model of the clauses and the assumptions" label))
          (ok (equal (list model t) (multiple-value-list (session-model s)))
              (format nil "~A: SESSION-MODEL" label))
          (ok (equal '(nil nil) (multiple-value-list (session-unsat-core s)))
              (format nil "~A: no core after SAT" label)))
        (progn
          (ok (null model))
          (ok (equal '(nil nil) (multiple-value-list (session-model s)))
              (format nil "~A: no model after UNSAT" label))
          (multiple-value-bind (core found) (session-unsat-core s)
            (ok (and found (core-ok-p core assumptions clauses vars))
                (format nil "~A: the final conflict is a core" label)))
          (multiple-value-bind (core found) (session-unsat-core s :minimal t)
            (ok (and found (core-ok-p core assumptions clauses vars) (core-minimal-p core clauses vars))
                (format nil "~A: a minimal core ~S" label core))
            (ok (equal (list core t) (multiple-value-list (session-unsat-core s)))
                (format nil "~A: the minimal core is stored" label)))
          (ok (equal '(nil nil) (multiple-value-list (session-model s)))
              (format nil "~A: SESSION-UNSAT-CORE leaves SESSION-MODEL alone" label))))
    sat))

(defun check-minimize-step (s rng vars clauses assumptions lex strategy label)
  "One SESSION-MINIMIZE of a random objective (two levels when LEX): the cost
against brute force and the fresh MINIMIZE, the model, then a SESSION-SOLVE that
assumes every objective literal (no bound of the call may survive it)."
  (let* ((objective (if lex
                        (list :lex
                              (random-objective* rng vars (1+ (rng-int rng 4)))
                              (random-objective* rng vars (1+ (rng-int rng 4))))
                        (random-objective* rng vars (1+ (rng-int rng 6)))))
         (expected (brute-optimum-over clauses vars objective assumptions))
         (fresh (fresh-minimize s objective assumptions strategy))
         (result (multiple-value-list
                  (session-minimize s objective :assumptions assumptions :strategy strategy))))
    (destructuring-bind (&optional model cost optimal-p &rest more) result
      (declare (ignore more))
      (ok (equal expected cost) (format nil "~A: the optimum ~S" label expected))
      (ok (equal (second fresh) cost) (format nil "~A: the fresh MINIMIZE's cost" label))
      (if cost
          (progn
            (ok (eq t optimal-p) (format nil "~A: proven" label))
            (ok (and (model-shape-ok-p model vars) (model-satisfies-p model clauses assumptions)
                     (equal cost (model-cost objective model)))
                (format nil "~A: a model of that cost" label))
            (ok (equal (list model t) (multiple-value-list (session-model s)))
                (format nil "~A: SESSION-MODEL" label)))
          (progn
            (ok (= 2 (length result)) (format nil "~A: UNSAT is exactly two values" label))
            (multiple-value-bind (core found) (session-unsat-core s)
              (ok (and found (core-ok-p core assumptions clauses vars))
                  (format nil "~A: a core of the assumptions" label)))))
      (check-solve-step s vars clauses (objective-literals objective)
                        (format nil "~A, every objective literal" label))
      cost)))

(defun session-script (seed &key (steps 40) (max-vars 9) (calls '(:solve)) (strategy :linear-bdd))
  "A random interleaving on a fresh session of *SAT-BACKEND*: add variables, add
clauses, and calls drawn from CALLS (:SOLVE, :MINIMIZE, :LEX), each checked.
Returns (values SAT UNSAT): the statuses of the SESSION-SOLVE calls seen."
  (let ((rng (make-rng seed)) (vars '()) (clauses '()) (sat 0) (unsat 0))
    (with-sat-session (s)
      (dotimes (step steps)
        (let ((op (rng-int rng 10))
              (label (format nil "seed ~D step ~D" seed step)))
          (cond ((or (null vars) (and (< (length vars) max-vars) (< op 2)))
                 (let* ((k (min (1+ (rng-int rng 2)) (- max-vars (length vars))))
                        (before (session-variable-count s))
                        (new (session-add-variables s k)))
                   (ok (equal (loop for i from (1+ before) repeat k collect i) new)
                       (format nil "~A: fresh consecutive indices" label))
                   (setf vars (append vars new))))
                ((< op 5)
                 (let ((new (loop repeat (1+ (rng-int rng 3))
                                  collect (random-clause* rng vars (1+ (rng-int rng 3))))))
                   (ok (eq s (session-add-clauses s new)))
                   (setf clauses (append clauses new))))
                (t
                 (let ((assumptions (random-literals* rng vars (rng-int rng 4)))
                       (kind (nth (rng-int rng (length calls)) calls)))
                   (if (eq kind :solve)
                       (if (check-solve-step s vars clauses assumptions label) (incf sat) (incf unsat))
                       (check-minimize-step s rng vars clauses assumptions (eq kind :lex)
                                            strategy label))))))))
    (values sat unsat)))

;;; ---------------------------------------------------------- equivalence

(define-session-check session-solve-equivalence
  (let ((sat 0) (unsat 0))
    (dolist (seed '(301 302 303 304 305))
      (multiple-value-bind (s u) (session-script seed :steps 45)
        (incf sat s)
        (incf unsat u)))
    (ok (and (plusp sat) (plusp unsat)) (format nil "both outcomes: ~D SAT, ~D UNSAT" sat unsat))))

(define-session-check session-minimize-equivalence
  ;; Each strategy; plain and :lex objectives interleaved with solves.
  (dolist (strategy *strategies*)
    (dolist (seed '(311 312))
      (session-script seed :steps 36 :calls '(:solve :minimize :minimize :lex) :strategy strategy))))

(define-session-check session-assumptions-per-call
  (with-sat-session (s)
    (session-add-variables s 3)
    (session-add-clauses s '((1 2) (-1 3)))
    (ok (null (nth-value 1 (session-solve s :assumptions '(-2 -1)))))
    (ok (nth-value 1 (session-solve s)) "the last call's assumptions are gone")
    (ok (null (nth-value 1 (session-solve s :assumptions '(1 -3)))))
    (multiple-value-bind (model sat) (session-solve s :assumptions '(1))
      (ok (and sat (member 3 model)) "1 implies 3"))
    (ok (equal '((1 -2 3) 2 t)
               (multiple-value-list (session-minimize s '((1 . 2) (2 . 3)) :assumptions '(1))))
        "under the assumption 1: 3 is forced")
    (ok (equal '((-1 2 -3) 1 t) (multiple-value-list (session-minimize s '((1 . 2) (2 . 3)))))
        "without it: the unique optimum")
    (ok (nth-value 1 (session-solve s :assumptions '(1))) "no bound of MINIMIZE survives")))

;;; -------------------------------------------------- variables and clauses

(define-session-check session-variables
  (with-sat-session (s)
    (ok (eql 0 (session-variable-count s)))
    (ok (equal '(nil t) (multiple-value-list (session-solve s))) "nothing to bind: (values NIL T)")
    (ok (null (session-add-variables s 0)))
    (ok (equal '(1 2 3) (session-add-variables s 3)))
    (ok (equal '(4) (session-add-variables s 1)))
    (ok (eql 4 (session-variable-count s)))
    (ok (signals (session-add-variables s -1) 'type-error))
    (ok (signals (session-add-variables s 1.5) 'type-error))
    (ok (signals (session-add-variables s nil) 'type-error))
    (ok (eql 4 (session-variable-count s)))
    (session-add-clauses s '((2)))
    (ok (equal '((-1 2 -3 -4) t) (multiple-value-list (session-solve s)))
        "every user variable, unassigned ones false")
    (ok (equal '(1 2 3 4) (mapcar #'abs (session-solve s :assumptions '(4 3))))
        "index order")))

(define-session-check session-add-clauses-errors
  (with-sat-session (s)
    (session-add-variables s 3)
    (session-add-clauses s '((1 2)))
    (dolist (bad (list '((0)) '((4)) '((-4)) '((1 x)) '((1.0)) '(5) 7 :clause))
      (ok (signals (session-add-clauses s bad) 'sat-invalid-formula) (format nil "~S" bad)))
    (ok (signals (session-add-clauses s (list '(3) '(9))) 'sat-invalid-formula))
    (ok (equal '((1 2)) (cnf-clauses (session-cnf s))) "nothing is added on a signal")
    (ok (eql 9 (handler-case (session-add-clauses s '((3) (1 9)))
                 (sat-invalid-formula (c) (sat-invalid-formula-datum c))))
        "DATUM: the bad literal")
    (ok (signals (session-add-clauses s (sat-or (sat-var 1) (sat-var 9))) 'sat-invalid-formula)
        "a formula variable beyond the session")
    (ok (equal "a" (handler-case (session-add-clauses s (sat-or (sat-var 1) (sat-var "a")))
                     (sat-invalid-formula (c) (sat-invalid-formula-datum c))))
        "a formula variable that is not a user variable: DATUM, its name")
    (session-add-clauses s (sat-exactly-one (mapcar #'sat-var '(1 2 3)) :encoding :sequential))
    (let* ((cnf (session-cnf s))
           (aux (find-if (lambda (i) (cnf-aux-variable-p cnf i))
                         (loop for i from 1 to (cnf-variable-count cnf) collect i)))
           (count (cnf-clause-count cnf)))
      (ok aux "the sequential encoding allocated an auxiliary")
      (ok (signals (session-add-clauses s (sat-var aux)) 'sat-invalid-formula)
          "an auxiliary is not a user variable")
      (ok (eql count (cnf-clause-count (session-cnf s))))
      (ok (session-add-clauses s (list (list aux (- aux)))) "an integer clause may name an auxiliary"))
    (ok (eq s (session-add-clauses s '())) "no clause")
    (ok (eq s (session-add-clauses s (sat-true))) "a formula with no clause")
    (ok (nth-value 1 (session-solve s)) "the session still answers")))

(define-session-check session-call-argument-errors
  (with-sat-session (s)
    (session-add-variables s 3)
    (session-add-clauses s '((1 2)))
    (ok (signals (session-solve s :assumptions '(4)) 'sat-invalid-formula))
    (ok (signals (session-solve s :assumptions '(0)) 'sat-invalid-formula))
    (ok (signals (session-solve s :assumptions '(one)) 'sat-invalid-formula))
    (ok (signals (session-solve s :budget -1) 'type-error))
    (ok (signals (session-solve s :budget 1.5) 'type-error))
    (ok (signals (session-minimize s '((1 . 4))) 'sat-invalid-formula))
    (ok (signals (session-minimize s '((1 . 1)) :assumptions '(-9)) 'sat-invalid-formula))
    (ok (signals (session-minimize s '((-1 . 1))) 'type-error))
    (ok (signals (session-minimize s '((1.5 . 1))) 'type-error))
    (ok (signals (session-minimize s '(1)) 'type-error))
    (ok (signals (session-minimize s '(:lex)) 'type-error))
    (ok (signals (session-minimize s '((1 . 1)) :strategy :fastest) 'type-error))
    (ok (signals (session-minimize s '((1 . 1)) :budget -1) 'type-error))
    (ok (equal '((-1 2 -3) 0 t) (multiple-value-list (session-minimize s '((1 . 1)))))
        "the session still answers")))

(define-session-check session-formula-clauses
  ;; Cardinality and PB constraints through each encoding: under every
  ;; complete assumption cube, the status is the formula's value.
  (dolist (encoding '(:auto :pairwise :sequential :totalizer :bdd))
    (with-sat-session (s)
      (let* ((vars (session-add-variables s 5))
             (x (mapcar #'sat-var vars))
             (formula (sat-and (sat-at-most-k x 2 :encoding encoding)
                               (sat-at-least-k (subseq x 0 3) 2 :encoding encoding)
                               (sat-pb-at-most (list (cons 2 (first x)) (cons 3 (fourth x))
                                                     (cons 1 (sat-not (fifth x))))
                                               3 :encoding encoding)))
             (mismatches 0) (models 0))
        (session-add-clauses s formula)
        (ok (equal (cnf-clauses (to-cnf formula :cnf (clauses->cnf '() 5)))
                   (cnf-clauses (session-cnf s)))
            (format nil "~A: TO-CNF's clauses" encoding))
        (dolist (env (all-assignments vars))
          (let ((cube (mapcar (lambda (p) (if (cdr p) (car p) (- (car p)))) env)))
            (multiple-value-bind (model sat) (session-solve s :assumptions cube)
              (unless (eq sat (formula-eval formula env)) (incf mismatches))
              (when sat
                (incf models)
                (unless (equal (sort (copy-list cube) #'< :key #'abs) model) (incf mismatches))))))
        (ok (zerop mismatches) (format nil "~A: every cube" encoding))
        (ok (plusp models))
        (multiple-value-bind (model sat) (session-solve s)
          (ok (and sat (model-shape-ok-p model vars)
                   (formula-eval formula (lambda (v) (values (literal-true-p v model) t))))
              (format nil "~A: a model of the formula, user variables only" encoding)))
        (ok (eq (nth-value 1 (session-solve s :assumptions '(-1))) (fresh-solve-status s '(-1))))))))

(define-session-check session-cnf-copy
  (with-sat-session (s)
    (session-add-variables s 3)
    (session-add-clauses s '((1 2) (-3)))
    (let ((cnf (session-cnf s)))
      (ok (cnf-p cnf))
      (ok (equal '((1 2) (-3)) (cnf-clauses cnf)))
      (ok (equal '(1 2 3) (cnf-user-variables cnf)))
      (ok (equal '(1 2 3) (mapcar (lambda (name) (cnf-variable-index cnf name)) '(1 2 3)))
          "user variable i is named i")
      (cnf-add-clause cnf '(3))
      (ok (eql 2 (cnf-clause-count (session-cnf s))) "a fresh copy"))
    (let ((formula (sat-exactly-one (mapcar #'sat-var '(1 2 3)) :encoding :totalizer)))
      (session-add-clauses s formula)
      (let ((cnf (session-cnf s)))
        (ok (equal (cnf-clauses (to-cnf formula :cnf (clauses->cnf '((1 2) (-3)) 3)))
                   (cnf-clauses cnf))
            "the formula as TO-CNF adds it")
        (ok (eql (session-variable-count s) (cnf-variable-count cnf)))
        (ok (every (lambda (i) (cnf-aux-variable-p cnf i))
                   (loop for i from 4 to (cnf-variable-count cnf) collect i))
            "encoding auxiliaries are unnamed")))
    (ok (nth-value 1 (session-solve s)) "satisfiable: 1 or 2 alone")))

(define-session-check session-empty-clause
  (with-sat-session (s)
    (session-add-variables s 2)
    (session-add-clauses s '((1 2)))
    (ok (nth-value 1 (session-solve s)))
    (session-add-clauses s '(()))
    (dolist (a '(() (1) (-1 -2) (2 2)))
      (ok (equal '(nil nil) (multiple-value-list (session-solve s :assumptions a))) (format nil "~S" a))
      (multiple-value-bind (core found) (session-unsat-core s)
        (ok (and found (subsequence-p core a))))
      (ok (equal '(nil t) (multiple-value-list (session-unsat-core s :minimal t)))
          "the clauses alone: the minimal core is NIL"))
    (ok (equal '(nil nil) (multiple-value-list (session-minimize s '((1 . 1))))))
    (session-add-clauses s '((1)))
    (ok (equal '(nil nil) (multiple-value-list (session-solve s))) "for good")))

;;; ------------------------------------------------------- results, cores

(define-session-check session-model-and-core-lifecycle
  (with-sat-session (s)
    (ok (equal '(nil nil) (multiple-value-list (session-model s))) "before any call")
    (ok (equal '(nil nil) (multiple-value-list (session-unsat-core s))))
    (session-add-variables s 2)
    (session-add-clauses s '((1 2)))
    (ok (equal '((-1 2) t) (multiple-value-list (session-solve s :assumptions '(-1)))))
    (ok (equal '((-1 2) t) (multiple-value-list (session-model s))))
    (setf (first (session-model s)) 99)
    (ok (equal '((-1 2) t) (multiple-value-list (session-model s))) "a fresh copy")
    (ok (null (nth-value 1 (session-solve s :assumptions '(-1 -2)))))
    (ok (equal '(nil nil) (multiple-value-list (session-model s))))
    (multiple-value-bind (core found) (session-unsat-core s)
      (ok (and found (equal '(-1 -2) core)) "both assumptions are needed"))
    (session-add-variables s 1)
    (ok (equal '(nil nil) (multiple-value-list (session-unsat-core s))) "SESSION-ADD-VARIABLES clears it")
    (ok (equal '(nil nil) (multiple-value-list (session-solve s :assumptions '(-2 -1)))))
    (session-add-clauses s '((3)))
    (ok (equal '(nil nil) (multiple-value-list (session-unsat-core s))) "SESSION-ADD-CLAUSES clears it")
    (session-solve s)
    (session-add-clauses s '((-3 1)))
    (ok (equal '(nil nil) (multiple-value-list (session-model s))) "so does a clause for the model")
    (ok (equal '((1 -2 3) 0 t) (multiple-value-list (session-minimize s '((1 . 2))))))
    (ok (equal '((1 -2 3) t) (multiple-value-list (session-model s))) "SESSION-MINIMIZE's model")))

(define-session-check session-minimal-cores
  (with-sat-session (s)
    (session-add-variables s 6)
    (session-add-clauses s '((-1 2) (-2 3) (-3 -4)))
    (ok (equal '(nil nil) (multiple-value-list (session-solve s :assumptions '(5 1 6 4)))))
    (multiple-value-bind (core found) (session-unsat-core s)
      (ok (and found (subsequence-p core '(5 1 6 4)) (member 1 core) (member 4 core))))
    (ok (equal '((1 4) t) (multiple-value-list (session-unsat-core s :minimal t)))
        "the only minimal core")
    (ok (equal '((1 4) t) (multiple-value-list (session-unsat-core s))) "stored")
    (session-solve s :assumptions '(4 1 1 4 5))
    (multiple-value-bind (core found) (session-unsat-core s :minimal t)
      (ok (and found (or (equal core '(1 4)) (equal core '(4 1))))
          (format nil "repeated assumptions: one copy of each, in the given order: ~S" core)))
    (session-solve s :assumptions '(2 -2 1 4))
    (multiple-value-bind (core found) (session-unsat-core s :minimal t)
      (ok (and found (or (equal core '(2 -2)) (equal core '(1 4)) (equal core '(2 4))
                         (equal core '(-2 1))))
          (format nil "a minimal core, given order: ~S" core)))))

;;; ------------------------------------------------------- closing

(define-session-check session-closed
  (let ((s (make-sat-session)))
    (session-add-variables s 2)
    (session-add-clauses s '((1 2)))
    (session-solve s)
    (ok (session-open-p s))
    (ok (eq *sat-backend* (session-backend s)))
    (ok (eq t (close-session s)))
    (ok (null (close-session s)) "closing twice: NIL")
    (ok (not (session-open-p s)))
    (ok (eq *sat-backend* (session-backend s)) "the readers still work")
    (session-backend-state s)
    (flet ((closed-p (thunk)
             (handler-case (progn (funcall thunk) nil)
               (sat-session-closed (c) (eq s (sat-session-closed-session c)))))
           (use-closed (thunk)
             (handler-bind ((sat-session-closed (lambda (c) (use-value :closed c))))
               (multiple-value-list (funcall thunk)))))
      (loop for (label thunk values) in
            (list (list "session-solve" (lambda () (session-solve s)) '(:closed nil))
                  (list "session-minimize" (lambda () (session-minimize s '((1 . 1)))) '(:closed nil))
                  (list "session-model" (lambda () (session-model s)) '(:closed nil))
                  (list "session-unsat-core" (lambda () (session-unsat-core s)) '(:closed nil))
                  (list "session-add-clauses" (lambda () (session-add-clauses s '((1)))) '(:closed))
                  (list "session-add-variables" (lambda () (session-add-variables s 1)) '(:closed))
                  (list "session-variable-count" (lambda () (session-variable-count s)) '(:closed))
                  (list "session-cnf" (lambda () (session-cnf s)) '(:closed)))
            do (ok (closed-p thunk) (format nil "~A signals SAT-SESSION-CLOSED" label))
               (ok (equal values (use-closed thunk)) (format nil "~A: USE-VALUE" label))))
    (ok (typep (make-condition 'sat-session-closed :session s) 'sat-error))
    (ok (search "closed" (princ-to-string (make-condition 'sat-session-closed :session s))))))

(define-session-check session-with-macro
  (let ((kept nil))
    (ok (equal '(:a :b) (multiple-value-list
                         (with-sat-session (s)
                           (setf kept s)
                           (session-add-variables s 1)
                           (values :a :b)))))
    (ok (not (session-open-p kept)) "closed after a normal exit")
    (block out
      (with-sat-session (s)
        (setf kept s)
        (return-from out)))
    (ok (not (session-open-p kept)) "closed after a non-local exit")
    (ok (eq :caught (handler-case (with-sat-session (s) (setf kept s) (error "boom"))
                      (error () :caught))))
    (ok (not (session-open-p kept)) "closed after an error")
    (let ((backend *sat-backend*))
      (with-sat-session (s :backend backend)
        (ok (eq backend (session-backend s)))))))

;;; ------------------------------------------------------- budgets

(define-session-check session-solve-budget
  (multiple-value-bind (clauses n) (pigeonhole 4 3)
    (let ((s (session-from-clauses clauses n)))
      (unwind-protect
           (progn
             (ok (signals (session-solve s :budget 0) 'sat-budget-exceeded))
             (ok (equal '(:gave-up nil)
                        (handler-bind ((sat-budget-exceeded (lambda (c) (use-value :gave-up c))))
                          (multiple-value-list (session-solve s :budget 0)))))
             (ok (equal '(nil nil) (multiple-value-list (session-model s))) "a USE-VALUE exit stores nothing")
             (ok (equal '(nil nil) (multiple-value-list (session-unsat-core s))))
             (ok (equal '(nil nil) (multiple-value-list (session-solve s))) "the next call: UNSAT")
             (ok (equal '(nil t) (multiple-value-list (session-unsat-core s))) "no assumption, the core NIL")
             (ok (equal '(nil nil) (handler-bind ((sat-budget-exceeded #'continue))
                                     (multiple-value-list (session-solve s :budget 1))))))
        (close-session s))))
  (let* ((rng (make-rng 2024))
         (clauses (loop for c = (random-3sat rng 12 40)
                        when (brute-satisfiable-p c 12) return c))
         (s (session-from-clauses clauses 12)))
    (unwind-protect
         (progn
           (ok (eq :gave-up (handler-bind ((sat-budget-exceeded (lambda (c) (use-value :gave-up c))))
                              (session-solve s :budget 0))))
           (multiple-value-bind (model sat) (session-solve s)
             (ok (and sat (model-satisfies-p model clauses)) "after the exit, a model"))
           (ok (null (signals (session-solve s) 'sat-budget-exceeded)) "budgets are per call")
           (multiple-value-bind (model sat)
               (handler-bind ((sat-budget-exceeded
                                (lambda (c) (store-value (1+ (sat-budget-exceeded-budget c)) c))))
                 (session-solve s :budget 0 :assumptions '(-1 2)))
             (ok (eq (brute-sat-over-p clauses (loop for i from 1 to 12 collect i) '(-1 2)) sat))
             (when sat (ok (model-satisfies-p model clauses '(-1 2))))))
      (close-session s))))

(defun chain-session-fixture (chain)
  "(values session cnf objective): CHAIN's clause-shaped CNF as a session, its
objective over the session's literals."
  (let* ((cnf (to-cnf (chain-formula chain)))
         (s (session-from-cnf cnf)))
    (values s cnf (index-objective cnf (chain-objective chain)))))

(defun check-session-chain-result (label chain cnf model cost optimal-p)
  (check-chain-result label chain (literals->names cnf model) cost optimal-p))

(define-session-check session-minimize-budget-no-model
  (dolist (strategy *strategies*)
    (let ((c (first (hint-chains))))
      (multiple-value-bind (s cnf objective) (chain-session-fixture c)
        (unwind-protect
             (progn
               (ok (signals (session-minimize s objective :strategy strategy :budget 0)
                            'sat-budget-exceeded))
               (ok (equal '(0 nil)
                          (handler-case (session-minimize s objective :strategy strategy :budget 0)
                            (sat-budget-exceeded (e)
                              (list (sat-budget-exceeded-budget e) (sat-budget-exceeded-timeout e)))))
                   "the decision budget ran out")
               (ok (equal '(:gave-up nil)
                          (handler-bind ((sat-budget-exceeded (lambda (e) (use-value :gave-up e))))
                            (multiple-value-list
                             (session-minimize s objective :strategy strategy :budget 0)))))
               (ok (equal '(nil nil) (multiple-value-list (session-model s))))
               (let ((signals 0))
                 (multiple-value-bind (model cost optimal-p)
                     (handler-bind ((sat-budget-exceeded (lambda (e) (incf signals) (continue e))))
                       (session-minimize s objective :strategy strategy :budget 0))
                   (ok (plusp signals))
                   (ok model "CONTINUE goes on until a model is found")
                   (when model
                     (check-session-chain-result (format nil "~A continue" strategy)
                                                 c cnf model cost optimal-p))))
               (multiple-value-bind (model cost optimal-p) (session-minimize s objective :strategy strategy)
                 (ok (eql (first (chain-dp c)) cost) (format nil "~A: then the optimum" strategy))
                 (ok (eq t optimal-p))
                 (check-session-chain-result (format nil "~A unbudgeted" strategy)
                                             c cnf model cost optimal-p)))
          (close-session s))))))

(define-session-check session-minimize-budget-sweep
  ;; Budgets 0..24 on fresh sessions: no model (SAT-BUDGET-EXCEEDED), an
  ;; unproven incumbent (unhandled SAT-BUDGET-REACHED), or a proven optimum.
  (dolist (strategy *strategies*)
    (let ((none 0) (unproven 0))
      (dolist (c (subseq (hint-chains) 0 4))
        (loop for budget from 0 to 24
              do (multiple-value-bind (s cnf objective) (chain-session-fixture c)
                   (unwind-protect
                        (multiple-value-bind (model cost optimal-p)
                            (handler-case (session-minimize s objective :strategy strategy :budget budget)
                              (sat-budget-exceeded () (values :no-model nil nil)))
                          (if (eq model :no-model)
                              (incf none)
                              (progn
                                (unless optimal-p (incf unproven))
                                (check-session-chain-result (format nil "~A budget ~D" strategy budget)
                                                            c cnf model cost optimal-p))))
                     (close-session s)))))
      (ok (plusp none) (format nil "~A: small budgets find no model" strategy))
      (ok (plusp unproven) (format nil "~A: some budget returns an unproven incumbent" strategy)))))

(defun unproven-budget (chain strategy)
  "The least budget in 0..40 at which SESSION-MINIMIZE on a fresh session of
CHAIN returns an unproven incumbent, or NIL."
  (loop for budget from 0 to 40
        thereis (multiple-value-bind (s cnf objective) (chain-session-fixture chain)
                  (declare (ignore cnf))
                  (unwind-protect
                       (multiple-value-bind (model cost optimal-p)
                           (handler-case (session-minimize s objective :strategy strategy :budget budget)
                             (sat-budget-exceeded () (values nil nil t)))
                         (declare (ignore model))
                         (and cost (not optimal-p) budget))
                    (close-session s)))))

(define-session-check session-minimize-budget-reached
  (dolist (strategy *strategies*)
    (let ((pair (loop for c in (hint-chains)
                      for b = (unproven-budget c strategy)
                      when b return (cons c b))))
      (ok pair (format nil "~A: a chain and a budget with an unproven incumbent" strategy))
      (when pair
        (destructuring-bind (c . budget) pair
          (flet ((run (handler)
                   ;; (list model cost optimal-p signals) on a fresh session;
                   ;; SIGNALS: (budget cost error-p use-best continue store-value) per signal
                   (multiple-value-bind (s cnf objective) (chain-session-fixture c)
                     (declare (ignore cnf))
                     (let ((signals '()))
                       (unwind-protect
                            (multiple-value-bind (model cost optimal-p)
                                (handler-bind ((sat-budget-reached
                                                 (lambda (r)
                                                   (push (list (sat-budget-reached-budget r)
                                                               (sat-budget-reached-cost r)
                                                               (typep r 'error)
                                                               (and (find-restart 'use-best r) t)
                                                               (and (find-restart 'continue r) t)
                                                               (and (find-restart 'store-value r) t))
                                                         signals)
                                                   (when handler (funcall handler r)))))
                                  (session-minimize s objective :strategy strategy :budget budget))
                              (list model cost optimal-p (reverse signals)
                                    (multiple-value-list (session-model s))))
                         (close-session s))))))
            (let* ((label (format nil "~A budget ~D" strategy budget))
                   (declined (run nil))
                   (best (run #'use-best))
                   (more (run #'continue))
                   (stored (run (lambda (r) (store-value 1000000 r))))
                   (optimum (first (chain-dp c))))
              (destructuring-bind (model cost optimal-p signals stored-model) declined
                (ok (and cost (null optimal-p)) (format nil "~A: unhandled, the unproven incumbent" label))
                (ok (= 1 (length signals)) (format nil "~A: signalled once" label))
                (ok (equal (list budget cost nil t t t) (first signals))
                    (format nil "~A: BUDGET, the incumbent's COST, not an error, three restarts" label))
                (ok (equal (list model t) stored-model) (format nil "~A: SESSION-MODEL" label))
                (ok (equal (list model cost nil) (subseq best 0 3)) (format nil "~A: USE-BEST" label))
                (ok (= 1 (length (fourth best)))))
              (destructuring-bind (model cost optimal-p signals stored-model) more
                (declare (ignore model stored-model))
                (ok (and (eql optimum cost) (eq t optimal-p)) (format nil "~A: CONTINUE, the optimum" label))
                (ok (plusp (length signals)))
                (when (second signals)
                  (ok (eql (* 2 (max budget 1)) (first (second signals))) "CONTINUE doubles the budget")))
              (destructuring-bind (model cost optimal-p signals stored-model) stored
                (declare (ignore model stored-model))
                (ok (and (eql optimum cost) (eq t optimal-p)) (format nil "~A: STORE-VALUE" label))
                (ok (= 1 (length signals)))))))))))

;;; ------------------------------------------------------- stress

(defun planted-binary (rng planted u v)
  "A random clause over U and V that PLANTED (variable -> boolean) satisfies."
  (let ((a (if (zerop (rng-int rng 2)) u (- u)))
        (b (if (zerop (rng-int rng 2)) v (- v))))
    (flet ((true-p (l) (eq (gethash (abs l) planted) (plusp l))))
      (if (or (true-p a) (true-p b)) (list a b) (list a (- b))))))

(define-session-check session-stress-many-steps
  ;; 240 incremental steps on one session: a variable and one or two binary
  ;; clauses (planted, so satisfiable; 2-SAT keeps the fresh oracle fast) per
  ;; step, a solve under random assumptions every 6 steps and a minimize of the
  ;; newest variables every 40 (the fresh oracle with :LINEAR-TOTALIZER: the
  ;; default strategy's 0.1 descent is slow on 240 variables, sat-protocol#6).
  (let ((rng (make-rng 4242)) (vars '()) (clauses '()) (planted (make-hash-table))
        (sat 0) (unsat 0) (bad 0))
    (with-sat-session (s)
      (dotimes (step 240)
        (let ((v (first (session-add-variables s 1))))
          (setf (gethash v planted) (zerop (rng-int rng 2)))
          (when vars
            (let ((window (last vars 6)))
              (loop repeat (1+ (rng-int rng 2))
                    do (let ((c (planted-binary rng planted (nth (rng-int rng (length window)) window) v)))
                         (session-add-clauses s (list c))
                         (push c clauses)))))
          (setf vars (append vars (list v))))
        (when (zerop (mod (1+ step) 6))
          (let ((a (random-literals* rng vars (+ 2 (rng-int rng 2)))))
            (multiple-value-bind (model status) (session-solve s :assumptions a)
              (if status (incf sat) (incf unsat))
              (unless (eq status (fresh-solve-status s a)) (incf bad))
              (when (and status (not (and (model-shape-ok-p model vars)
                                          (model-satisfies-p model clauses a))))
                (incf bad)))))
        (when (zerop (mod (1+ step) 40))
          (let ((objective (mapcar (lambda (v) (cons (1+ (rng-int rng 3)) v)) (last vars 5))))
            (multiple-value-bind (model cost optimal-p) (session-minimize s objective)
              (ok (and (eq t optimal-p)
                       (eql cost (second (fresh-minimize s objective '() :linear-totalizer)))
                       (model-satisfies-p model clauses)
                       (eql cost (model-cost objective model)))
                  (format nil "step ~D: the optimum ~S" step cost)))))))
    (ok (zerop bad) (format nil "~D solves agree with the fresh SOLVE" (+ sat unsat)))
    (ok (and (plusp sat) (plusp unsat)) (format nil "both outcomes: ~D SAT, ~D UNSAT" sat unsat))))
