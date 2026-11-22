;;;; sat-protocol/conformance: the backend conformance suite (Rove).
;;;;
;;;; Every SAT backend's test system runs it with its own backend:
;;;;   (sat-protocol/conformance:run-conformance (make-instance 'my-backend))
;;;; or, to report it in one run with its own tests, binds
;;;; SAT-PROTOCOL:*SAT-BACKEND* and passes "sat-protocol/conformance" to
;;;; ROVE:RUN next to its own test system. The tests use *SAT-BACKEND*.
;;;;
;;;; Everything in this directory is GIVEN test code (no stubs), including the
;;;; REFERENCE-BACKEND oracle (cl-repository's naive search over CNF).

(defpackage #:sat-protocol/conformance
  (:use #:cl #:rove #:sat-protocol)
  (:export
   #:run-conformance
   #:reference-backend
   #:reference-search
   ;; helpers shared with backend test suites
   #:make-rng
   #:rng-int
   #:random-3sat
   #:pigeonhole
   #:clauses->cnf
   #:brute-models
   #:brute-satisfiable-p
   #:clauses-satisfied-p
   #:model->assignment
   #:true-names
   #:fixture-path
   #:version<
   #:var-precedes-p
   #:latest-first-order
   #:pkg-var
   #:package-formula
   #:f
   #:random-sexp
   #:sexp-eval
   #:sexp-vars
   #:all-assignments))

(in-package #:sat-protocol/conformance)

(defun run-conformance (backend &key (style :spec))
  "Run the conformance suite against BACKEND. Returns true when it passes."
  (let ((*sat-backend* backend))
    (rove:run "sat-protocol/conformance" :style style)))

(defun fixture-path (name)
  (asdf:system-relative-pathname "sat-protocol" (format nil "tests/fixtures/~A" name)))

;;; Deterministic PRNG (same sequence on every implementation): 31-bit LCG.

(defun make-rng (seed)
  (list (mod seed 2147483648)))

(defun rng-int (rng n)
  "A pseudo-random integer in [0, N)."
  (setf (car rng) (mod (+ (* 1103515245 (car rng)) 12345) 2147483648))
  (mod (ash (car rng) -8) n))

;;; Clause-level helpers. Clauses are lists of non-zero integers over 1..N.

(defun random-3sat (rng nvars nclauses)
  "NCLAUSES random clauses of 3 distinct variables out of 1..NVARS."
  (loop repeat nclauses
        collect (let ((vars nil))
                  (loop while (< (length vars) 3)
                        do (pushnew (1+ (rng-int rng nvars)) vars))
                  (mapcar (lambda (v) (if (zerop (rng-int rng 2)) v (- v))) vars))))

(defun pigeonhole (pigeons holes)
  "Clauses of PHP(PIGEONS, HOLES): variable (i-1)*HOLES + j = pigeon i in hole j.
Unsatisfiable iff PIGEONS > HOLES. Returns (values clauses nvars)."
  (flet ((v (i j) (+ (* (1- i) holes) j)))
    (values
     (append
      (loop for i from 1 to pigeons
            collect (loop for j from 1 to holes collect (v i j)))
      (loop for j from 1 to holes
            nconc (loop for i from 1 to pigeons
                        nconc (loop for k from (1+ i) to pigeons
                                    collect (list (- (v i j)) (- (v k j)))))))
     (* pigeons holes))))

(defun clauses->cnf (clauses nvars)
  "A CNF over variables named 1..NVARS (DIMACS style) with CLAUSES."
  (let ((cnf (make-cnf)))
    (loop for i from 1 to nvars do (cnf-ensure-variable cnf i))
    (dolist (c clauses cnf)
      (cnf-add-clause cnf c))))

(defun clauses-satisfied-p (clauses value-fn)
  "VALUE-FN: variable index -> boolean."
  (every (lambda (c)
           (some (lambda (l) (if (plusp l) (funcall value-fn l) (not (funcall value-fn (- l))))) c))
         clauses))

(defun brute-models (clauses nvars)
  "Every total assignment satisfying CLAUSES, as bit-vectors indexed 1..NVARS."
  (let ((models nil))
    (dotimes (bits (expt 2 nvars) (nreverse models))
      (let ((v (make-array (1+ nvars) :element-type 'bit :initial-element 0)))
        (loop for i from 1 to nvars do (setf (sbit v i) (ldb (byte 1 (1- i)) bits)))
        (when (clauses-satisfied-p clauses (lambda (i) (= 1 (sbit v i))))
          (push v models))))))

(defun brute-satisfiable-p (clauses nvars)
  (dotimes (bits (expt 2 nvars) nil)
    (when (clauses-satisfied-p clauses (lambda (i) (logbitp (1- i) bits)))
      (return t))))

(defun model->assignment (model)
  "A function name -> boolean over MODEL (unbound names are NIL)."
  (lambda (name) (cdr (assoc name model :test #'equal))))

(defun true-names (model)
  "Names bound to T in MODEL, sorted with STRING< on their printed form."
  (sort (loop for (name . value) in model when value collect name)
        #'string< :key #'princ-to-string))

;;; cl-repository's latest-version-first rule, copied from
;;; cl-repository src/client/version-utils.lisp and src/client/solver.lisp
;;; (MIT, (c) 2026 CommonLispNext) so the decision-order hook can be checked
;;; against it without depending on cl-repository.

(defun %split-version-segments (value)
  (let ((segments nil) (start nil))
    (flet ((emit (end)
             (when start
               (push (subseq value start end) segments)
               (setf start nil))))
      (loop for idx from 0 below (length value)
            for ch = (char value idx)
            do (if (or (alpha-char-p ch) (digit-char-p ch))
                   (unless start (setf start idx))
                   (emit idx)))
      (emit (length value)))
    (nreverse segments)))

(defun %segment-key (segment)
  (if (every #'digit-char-p segment)
      (list 1 (parse-integer segment))
      (list 0 (string-downcase segment))))

(defun %compare-segments (left right)
  (or (loop for a in left
            for b in right
            do (let ((ka (%segment-key a)) (kb (%segment-key b)))
                 (unless (equal ka kb)
                   (return (if (or (< (first ka) (first kb))
                                   (and (= (first ka) (first kb))
                                        (if (= (first ka) 1)
                                            (< (second ka) (second kb))
                                            (string< (second ka) (second kb)))))
                               -1
                               1)))))
      (let ((la (length left)) (lb (length right)))
        (cond ((< la lb) -1) ((> la lb) 1) (t 0)))))

(defun version< (left right)
  (< (%compare-segments (%split-version-segments left)
                        (%split-version-segments right))
     0))

(defun %split-pkg-var (var-name)
  (let ((pos (search "-v" var-name :from-end t)))
    (if pos
        (values (subseq var-name 0 pos) (subseq var-name (+ pos 2)))
        (values var-name nil))))

(defun var-precedes-p (a b)
  "Package name, then version: cl-repository's VAR-PRECEDES-P."
  (multiple-value-bind (name-a ver-a) (%split-pkg-var a)
    (multiple-value-bind (name-b ver-b) (%split-pkg-var b)
      (cond ((string< name-a name-b) t)
            ((string> name-a name-b) nil)
            ((and ver-a ver-b) (version< ver-a ver-b))
            (t (string< a b))))))

(defun latest-first-order (names)
  "The :ORDER hook for cl-repository's heuristic: decide the greatest name
under VAR-PRECEDES-P (the highest version of the last package) first."
  (reduce (lambda (a b) (if (var-precedes-p a b) b a)) names))

(defun pkg-var (name version)
  (format nil "~A-v~A" name version))

(defun package-formula (&key root packages depends pins)
  "A formula in cl-repository's BUILD-FORMULA shape.
ROOT: (name version). PACKAGES: ((name version...) ...). DEPENDS:
((name version dep-name dep-version...) ...): NAME at VERSION needs one of the
listed versions of DEP-NAME. PINS: ((name version) ...) installed systems."
  (let ((terms (list (sat-var (apply #'pkg-var root)))))
    (dolist (pin pins)
      (push (sat-var (apply #'pkg-var pin)) terms))
    (dolist (p packages)
      (let ((vars (mapcar (lambda (v) (pkg-var (first p) v)) (rest p))))
        (loop for (v1 . more) on vars
              do (dolist (v2 more)
                   (push (sat-not (sat-and (sat-var v1) (sat-var v2))) terms)))))
    (dolist (d depends)
      (destructuring-bind (name version dep-name &rest dep-versions) d
        (push (sat-implies (sat-var (pkg-var name version))
                           (sat-or* (mapcar (lambda (v) (sat-var (pkg-var dep-name v)))
                                            dep-versions)))
              terms)))
    (sat-and* (nreverse terms))))

;;; Formula sexps, evaluated independently of sat-protocol (the oracle).

(defun f (sexp)
  "Shorthand: SEXP->FORMULA."
  (sexp->formula sexp))

(defun random-sexp (rng names depth)
  "A random formula sexp over NAMES using every operator."
  (if (or (zerop depth) (zerop (rng-int rng 4)))
      (let ((name (nth (rng-int rng (length names)) names)))
        (if (zerop (rng-int rng 3)) (list :not name) name))
      (ecase (rng-int rng 5)
        (0 (list :not (random-sexp rng names (1- depth))))
        (1 (list* :and (loop repeat (+ 2 (rng-int rng 2))
                             collect (random-sexp rng names (1- depth)))))
        (2 (list* :or (loop repeat (+ 2 (rng-int rng 2))
                            collect (random-sexp rng names (1- depth)))))
        (3 (list :implies (random-sexp rng names (1- depth)) (random-sexp rng names (1- depth))))
        (4 (list :iff (random-sexp rng names (1- depth)) (random-sexp rng names (1- depth)))))))

(defun sexp-eval (sexp env)
  "Truth value of SEXP; ENV is an alist name -> boolean (missing = NIL)."
  (cond ((eq sexp :true) t)
        ((eq sexp :false) nil)
        ((atom sexp) (cdr (assoc sexp env :test #'equal)))
        (t (ecase (first sexp)
             (:var (cdr (assoc (second sexp) env :test #'equal)))
             (:not (not (sexp-eval (second sexp) env)))
             (:and (every (lambda (s) (sexp-eval s env)) (rest sexp)))
             (:or (some (lambda (s) (sexp-eval s env)) (rest sexp)))
             (:implies (or (not (sexp-eval (second sexp) env)) (sexp-eval (third sexp) env)))
             (:iff (eq (not (sexp-eval (second sexp) env)) (not (sexp-eval (third sexp) env))))))))

(defun sexp-vars (sexp)
  "Variable names of SEXP in first-occurrence order."
  (let ((names nil))
    (labels ((walk (s)
               (cond ((member s '(:true :false)))
                     ((atom s) (pushnew s names :test #'equal))
                     ((eq (first s) :var) (pushnew (second s) names :test #'equal))
                     (t (mapc #'walk (rest s))))))
      (walk sexp))
    (nreverse names)))

(defun all-assignments (names)
  "Every alist assigning NAMES."
  (if (null names)
      (list nil)
      (loop for rest in (all-assignments (rest names))
            nconc (list (acons (first names) t rest)
                        (acons (first names) nil rest)))))
