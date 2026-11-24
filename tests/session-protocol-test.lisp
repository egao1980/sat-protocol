(in-package #:sat-protocol/tests)

;;; 0.3 (L2b-2) sessions: what the session GFs receive (session.lisp, "Call
;;; counts"), the stateless default methods against the fresh front ends (the
;;; same answers, exactly), the stateful session path on
;;; REFERENCE-SESSION-BACKEND, and the conformance session checks run again on
;;; it.

(defclass session-recorder (reference-backend)
  ((log :initform nil :accessor recorder-log))
  (:default-initargs :propagate t)
  (:documentation "The propagating reference search, recording (newest first) a
list (GF . arguments) per session GF and per BACKEND-SOLVE /
BACKEND-FINAL-CONFLICT / BACKEND-MINIMIZE call. CNF arguments are recorded as
their clause lists at the time of the call."))

(defclass stateful-recorder (reference-session-backend)
  ((log :initform nil :accessor recorder-log))
  (:documentation "REFERENCE-SESSION-BACKEND recording as SESSION-RECORDER."))

(defun record (backend entry)
  (push entry (recorder-log backend)))

(macrolet ((recording (class)
             `(progn
                (defmethod backend-session-open :around ((b ,class) session)
                  (record b (list 'backend-session-open session))
                  (call-next-method))
                (defmethod backend-session-close :around ((b ,class) session)
                  (record b (list 'backend-session-close session))
                  (call-next-method))
                (defmethod backend-session-add-clauses :around ((b ,class) session clauses)
                  (record b (list 'backend-session-add-clauses (copy-tree clauses)
                                  (session-variable-count session)))
                  (call-next-method))
                (defmethod backend-session-solve :around ((b ,class) session &rest args
                                                          &key &allow-other-keys)
                  (record b (list* 'backend-session-solve session args))
                  (call-next-method))
                (defmethod backend-session-final-conflict :around ((b ,class) session assumptions
                                                                   &rest args &key &allow-other-keys)
                  (record b (list* 'backend-session-final-conflict (copy-list assumptions) args))
                  (call-next-method))
                (defmethod backend-session-minimize :around ((b ,class) session objective
                                                             &rest args &key &allow-other-keys)
                  (record b (list* 'backend-session-minimize (copy-tree objective) args))
                  (call-next-method))
                (defmethod backend-solve :around ((b ,class) cnf &rest args &key &allow-other-keys)
                  (record b (list* 'backend-solve (cnf-clauses cnf) args))
                  (call-next-method))
                (defmethod backend-final-conflict :around ((b ,class) cnf assumptions
                                                           &rest args &key &allow-other-keys)
                  (record b (list* 'backend-final-conflict (cnf-clauses cnf) (copy-list assumptions) args))
                  (call-next-method))
                (defmethod backend-minimize :around ((b ,class) cnf objective &rest args
                                                     &key &allow-other-keys)
                  (declare (ignore cnf args))
                  (record b (list 'backend-minimize objective))
                  (call-next-method)))))
  (recording session-recorder)
  (recording stateful-recorder))

(defun calls-of (backend gf)
  "The recorded calls of GF, oldest first."
  (reverse (remove gf (recorder-log backend) :key #'first :test-not #'eq)))

(defun to-literals (model)
  "A name-level model over integer names -> the session's literal list."
  (mapcar (lambda (pair) (if (cdr pair) (car pair) (- (car pair)))) model))

;;; ---------------------------------------------------------------- opening

(deftest session-no-backend
  (let ((*sat-backend* nil))
    (ok (signals (make-sat-session) 'sat-no-backend))
    (let ((s (handler-bind ((sat-no-backend
                              (lambda (c) (use-backend (make-instance 'reference-backend) c))))
               (make-sat-session))))
      (ok (typep s 'sat-session))
      (ok (typep (session-backend s) 'reference-backend) "USE-BACKEND")
      (close-session s))
    (ok (eq :none (handler-bind ((sat-no-backend (lambda (c) (use-value :none c))))
                    (make-sat-session)))
        "USE-VALUE")))

(deftest session-open-and-close-calls
  (let* ((b (make-instance 'session-recorder))
         (s (make-sat-session :backend b)))
    (ok (eq b (session-backend s)) ":BACKEND")
    (ok (null (session-backend-state s)) "the default BACKEND-SESSION-OPEN: a stateless session")
    (ok (equal (list (list 'backend-session-open s)) (calls-of b 'backend-session-open)) "opened once")
    (close-session s)
    (close-session s)
    (ok (equal (list (list 'backend-session-close s)) (calls-of b 'backend-session-close)) "closed once"))
  (let ((b (make-instance 'stateful-recorder)))
    (with-sat-session (s :backend b)
      (ok (session-backend-state s) "a stateful session")
      (ok (session-open-p s) "BACKEND-SESSION-CLOSE runs while the session is open"))
    (ok (= 1 (length (calls-of b 'backend-session-close))))))

;;; ------------------------------------------------------------ the GF calls

(deftest session-add-clauses-calls
  (let ((b (make-instance 'session-recorder)))
    (with-sat-session (s :backend b)
      (session-add-variables s 3)
      (ok (null (calls-of b 'backend-session-add-clauses)) "variables alone: no call")
      (session-add-clauses s '((1 2) (-3) (2 2 -2)))
      (ok (equal '((backend-session-add-clauses ((1 2) (-3) (2 2 -2)) 3))
                 (calls-of b 'backend-session-add-clauses))
          "one call, exactly the clauses, the variables allocated first")
      (session-add-clauses s '())
      (session-add-clauses s (sat-true))
      (ok (= 1 (length (calls-of b 'backend-session-add-clauses))) "no clause: no call")
      (let ((formula (sat-at-most-k (mapcar #'sat-var '(1 2 3)) 1 :encoding :totalizer)))
        (session-add-clauses s formula)
        (let ((new (second (car (last (calls-of b 'backend-session-add-clauses)))))
              (all (cnf-clauses (session-cnf s))))
          (ok (equal new (subseq all 3)) "a formula: the clauses it added to the session CNF")
          (ok (equal (cnf-clauses (to-cnf formula :cnf (clauses->cnf '((1 2) (-3) (2 2 -2)) 3))) all))
          (ok (eql (session-variable-count s)
                   (third (car (last (calls-of b 'backend-session-add-clauses)))))
              "its auxiliaries allocated first"))))))

(deftest session-solve-calls
  (let ((b (make-instance 'session-recorder)))
    (with-sat-session (s :backend b)
      (session-add-variables s 3)
      (session-add-clauses s '((1 2) (-1 3)))
      (session-solve s :assumptions '(-2 3 3) :budget 50)
      (ok (equal '((backend-session-final-conflict (-2 3 3) :budget 50))
                 (mapcar (lambda (call) (list* (first call) (second call)
                                               (loop for (k v) on (cddr call) by #'cddr
                                                     when v nconc (list k v))))
                         (calls-of b 'backend-session-final-conflict)))
          "one BACKEND-SESSION-FINAL-CONFLICT: the assumptions as given, the budget")
      (destructuring-bind (&key order phase &allow-other-keys)
          (cddr (first (calls-of b 'backend-session-final-conflict)))
        (ok (and (null order) (null phase)) "ORDER and PHASE NIL"))
      (ok (equal '((backend-final-conflict ((1 2) (-1 3)) (-2 3 3)))
                 (mapcar (lambda (call) (subseq call 0 3)) (calls-of b 'backend-final-conflict)))
          "the stateless default: BACKEND-FINAL-CONFLICT on the session's clauses")
      (ok (eql 50 (getf (cdddr (first (calls-of b 'backend-final-conflict))) :budget)))
      (ok (null (calls-of b 'backend-session-solve))))))

(deftest session-minimize-calls
  (let ((b (make-instance 'session-recorder)))
    (with-sat-session (s :backend b)
      (session-add-variables s 3)
      (session-add-clauses s '((1 2) (-1 3)))
      (setf (recorder-log b) nil)
      (let ((before (cnf-clauses (session-cnf s))))
        (ok (equal '((-1 2 -3) 1 t) (multiple-value-list (session-minimize s '((1 . 2) (2 . 3))))))
        (session-minimize s '(:lex ((1 . 1)) ((1 . 2))) :strategy :core-guided :budget 1000
                          :assumptions '(3))
        (ok (equal '((backend-session-minimize ((1 . 2) (2 . 3)) :assumptions nil :strategy :linear-bdd
                      :budget nil)
                     (backend-session-minimize (:lex ((1 . 1)) ((1 . 2))) :assumptions (3)
                      :strategy :core-guided :budget 1000))
                   (mapcar (lambda (call) (list* (first call) (second call)
                                                 (loop for key in '(:assumptions :strategy :budget)
                                                       nconc (list key (getf (cddr call) key)))))
                           (calls-of b 'backend-session-minimize)))
            "one BACKEND-SESSION-MINIMIZE per call: the index-level objective, strategy, budget")
        (ok (null (calls-of b 'backend-session-add-clauses)) "the stateless default adds nothing")
        (ok (null (calls-of b 'backend-minimize)) "nor calls BACKEND-MINIMIZE")
        (ok (calls-of b 'backend-solve) "it searches with BACKEND-SOLVE")
        (ok (every (lambda (call) (equal before (subseq (second call) 0 (length before))))
                   (append (calls-of b 'backend-solve) (calls-of b 'backend-final-conflict)))
            "on copies of the session's clauses plus its own")
        (ok (equal before (cnf-clauses (session-cnf s))) "the session CNF gains nothing")
        (ok (eql 3 (session-variable-count s)))))))

;;; ---------------------------------------- stateless: the fresh front ends

(deftest stateless-session-solve-is-solve
  ;; The same backend on the same CNF: the same model, call after call.
  (let ((rng (make-rng 5151)) (calls 0) (unsat 0))
    (with-sat-session (s :backend (make-instance 'reference-backend :propagate t))
      (let ((vars (session-add-variables s 8)))
        (dotimes (step 30)
          (session-add-clauses s (list (random-clause* rng vars 3)))
          (let ((assumptions (random-literals* rng vars (rng-int rng 3))))
            (multiple-value-bind (model sat) (session-solve s :assumptions assumptions)
              (incf calls)
              (unless sat (incf unsat))
              (multiple-value-bind (fresh fresh-sat)
                  (solve (session-cnf s) :assumptions (mapcar #'lit-formula assumptions)
                                         :backend (session-backend s))
                (ok (eq fresh-sat sat))
                (ok (equal (and fresh-sat (to-literals fresh)) model)
                    (format nil "step ~D: SOLVE's model" step))))))))
    (ok (and (plusp unsat) (< unsat calls)) "both outcomes")))

(deftest stateless-minimal-core-is-unsat-core
  ;; Deletion over every assumption: UNSAT-CORE's result, element for element.
  (let ((rng (make-rng 6161)) (cores 0))
    (dotimes (i 30)
      (let ((clauses (random-3sat rng 7 14))
            (assumptions (random-literals* rng '(1 2 3 4 5 6 7) 5)))
        (with-sat-session (s :backend (make-instance 'reference-backend :propagate t))
          (session-add-variables s 7)
          (session-add-clauses s clauses)
          (unless (nth-value 1 (session-solve s :assumptions assumptions))
            (incf cores)
            (let* ((objects (mapcar #'lit-formula assumptions))
                   (expected (unsat-core (session-cnf s) :assumptions objects :backend (session-backend s))))
              (ok (equal (loop for a in assumptions for o in objects
                               when (member o expected) collect a)
                         (session-unsat-core s :minimal t))
                  (format nil "instance ~D" i)))))))
    (ok (plusp cores))))

(deftest stateless-session-minimize-is-minimize
  (dolist (strategy (list :linear-totalizer :stratified :core-guided))
    (dolist (c (random-chains 411 4 :positions 3 :levels 1))
      (multiple-value-bind (s cnf objective) (chain-session-fixture c)
        (unwind-protect
             (multiple-value-bind (model cost optimal-p)
                 (session-minimize s objective :strategy strategy)
               (multiple-value-bind (fresh fresh-cost fresh-optimal-p)
                   (minimize cnf (chain-objective c) :strategy strategy :backend (session-backend s))
                 (ok (equal (list fresh-cost fresh-optimal-p) (list cost optimal-p)))
                 (ok (equal (and fresh (to-literals (mapcar (lambda (pair)
                                                               (cons (cnf-variable-index cnf (car pair))
                                                                     (cdr pair)))
                                                             fresh)))
                            model)
                     "MINIMIZE's 0.2 search from scratch: its model")))
          (close-session s))))))

;;; -------------------------------------------------- the stateful defaults

(defclass half-stateful-backend (reference-backend) ()
  (:documentation "Opens a stateful session but specialises nothing else."))

(defmethod backend-session-open ((b half-stateful-backend) session)
  (declare (ignore session))
  :state)

(deftest stateful-default-methods-signal
  (with-sat-session (s :backend (make-instance 'half-stateful-backend))
    (ok (eq :state (session-backend-state s)))
    (ok (equal '(1 2) (session-add-variables s 2)))
    (ok (signals (session-add-clauses s '((1 2))) 'sat-error) "BACKEND-SESSION-ADD-CLAUSES")
    (ok (signals (session-solve s) 'sat-error) "BACKEND-SESSION-FINAL-CONFLICT")
    (ok (signals (backend-session-solve (session-backend s) s) 'sat-error) "BACKEND-SESSION-SOLVE")))

;;; ------------------------------------------- the stateful session path

(defun retired-guards-p (pushed before)
  "Every clause in PUSHED (lists of clauses, oldest first) contains the negation
of a variable above BEFORE whose unit clause (-v) is in PUSHED too."
  (let* ((clauses (apply #'append pushed))
         (retired (loop for c in clauses
                        when (and (= 1 (length c)) (minusp (first c)) (> (- (first c)) before))
                          collect (- (first c)))))
    (every (lambda (c)
             (some (lambda (l) (and (minusp l) (member (- l) retired))) c))
           clauses)))

(deftest stateful-session-path
  (dolist (strategy (list :linear-bdd :linear-totalizer :stratified :core-guided))
    (dolist (lex '(nil t))
      (let ((b (make-instance 'stateful-recorder))
            (c (first (random-chains 421 1 :positions 3 :levels 2))))
        (let* ((cnf (to-cnf (chain-formula c)))
               (s (session-from-cnf cnf :backend b))
               (objective (index-objective cnf (if lex
                                                   (chain-lex-objective c)
                                                   (chain-objective c))))
               (before (session-variable-count s))
               (clauses (cnf-clauses (session-cnf s)))
               (label (format nil "~A~:[~; :lex~]" strategy lex)))
          (unwind-protect
               (progn
                 (setf (recorder-log b) nil)
                 (multiple-value-bind (model cost optimal-p)
                     (session-minimize s objective :strategy strategy)
                   (ok (equal (if lex (chain-dp c) (first (chain-dp c))) cost)
                       (format nil "~A: the DP optimum" label))
                   (ok (eq t optimal-p))
                   (ok (model-satisfies-p model clauses)))
                 (ok (null (or (calls-of b 'backend-solve) (calls-of b 'backend-final-conflict)
                               (calls-of b 'backend-minimize)))
                     (format nil "~A: never the from-scratch GFs" label))
                 (ok (or (calls-of b 'backend-session-solve) (calls-of b 'backend-session-final-conflict))
                     (format nil "~A: the session's own GFs" label))
                 (let ((pushed (mapcar #'second (calls-of b 'backend-session-add-clauses))))
                   ;; :CORE-GUIDED with singleton cores only relaxes nothing.
                   (when (or lex (not (eq strategy :core-guided)))
                     (ok pushed (format nil "~A: the search adds clauses to the backend" label)))
                   (ok (retired-guards-p pushed before)
                       (format nil "~A: each one guarded by a selector retired before the return" label)))
                 (ok (equal clauses (cnf-clauses (session-cnf s))) "the session CNF gains no clause")
                 (let ((cnf (session-cnf s)))
                   (when (calls-of b 'backend-session-add-clauses)
                     (ok (< before (session-variable-count s)) "the search's variables are the session's"))
                   (ok (every (lambda (i) (cnf-aux-variable-p cnf i))
                              (loop for i from (1+ before) to (cnf-variable-count cnf) collect i))
                       "as auxiliaries"))
                 ;; Nothing of the call is left: every labelling is still a model.
                 (let ((worst (chain-worst-labelling c)))
                   (ok (nth-value 1 (session-solve s :assumptions
                                                   (loop for p from 0 for l in worst
                                                         collect (cnf-variable-index
                                                                  cnf (sat-protocol/conformance:chain-x p l)))))
                       (format nil "~A: the worst labelling is still allowed" label))))
            (close-session s)))))))

(deftest stateful-session-minimize-cut-short
  ;; A USE-VALUE exit and an exit from a SAT-BUDGET-REACHED handler retire the
  ;; call's selectors too.
  (let* ((b (make-instance 'stateful-recorder))
         (c (first (hint-chains)))
         (cnf (to-cnf (chain-formula c)))
         (s (session-from-cnf cnf :backend b))
         (objective (index-objective cnf (chain-objective c)))
         (before (session-variable-count s)))
    (unwind-protect
         (progn
           (setf (recorder-log b) nil)
           (ok (eq :stopped (block stop
                              (handler-bind ((sat-budget-reached (lambda (r) (declare (ignore r))
                                                                   (return-from stop :stopped))))
                                (handler-bind ((sat-budget-exceeded #'continue))
                                  (session-minimize s objective :budget 0))))))
           (ok (retired-guards-p (mapcar #'second (calls-of b 'backend-session-add-clauses)) before)
               "a throw from a handler")
           (setf before (session-variable-count s)
                 (recorder-log b) nil)
           (ok (eq :gave-up (handler-bind ((sat-budget-exceeded (lambda (e) (use-value :gave-up e))))
                              (session-minimize s objective :budget 0 :strategy :core-guided))))
           (ok (retired-guards-p (mapcar #'second (calls-of b 'backend-session-add-clauses)) before)
               "a USE-VALUE exit")
           (multiple-value-bind (model cost optimal-p) (session-minimize s objective)
             (declare (ignore model))
             (ok (and (eql (first (chain-dp c)) cost) optimal-p) "the session still answers")))
      (close-session s))))

(deftest stateful-reference-session-checks
  ;; Every conformance session check, on a stateful session.
  (run-session-checks (make-instance 'reference-session-backend :propagate t)))
