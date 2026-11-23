(in-package #:sat-protocol/tests)

;;; 0.2 cardinality and pseudo-Boolean constraints (src/cardinality.lisp):
;;; constructors and folding, the :AT-MOST node (readers, eval, sexp, assign),
;;; every encoding against brute-force enumeration, the CNF-level adders, nested
;;; and guarded (UNSAT-CORE :NAMED) occurrences.

(defparameter *encodings* '(:auto :pairwise :sequential :totalizer :bdd))

(defun vnames (n)
  (loop for i from 1 to n collect (format nil "v~D" i)))

(defun env-key (env names)
  (format nil "~{~:[0~;1~]~}" (mapcar (lambda (n) (cdr (assoc n env :test #'equal))) names)))

(defun projected-keys (formula names)
  "Models of FORMULA projected on NAMES, as sorted bit strings."
  (sort (mapcar (lambda (m) (env-key m names))
                (collect-models (solve-all formula :project names)))
        #'string<))

(defun brute-keys (names predicate)
  (sort (loop for env in (all-assignments names)
              when (funcall predicate env) collect (env-key env names))
        #'string<))

(defun random-literal (rng names)
  (let ((v (sat-var (nth (rng-int rng (length names)) names))))
    (if (zerop (rng-int rng 2)) v (sat-not v))))

(defun random-literals (rng names)
  "One literal per name (random polarity), sometimes plus a repeated or
complementary one."
  (let ((lits (mapcar (lambda (n)
                        (let ((v (sat-var n))) (if (zerop (rng-int rng 2)) v (sat-not v))))
                      names)))
    (if (zerop (rng-int rng 3))
        (append lits (list (random-literal rng names)))
        lits)))

(defun weighted (terms env)
  "Sum of the weights of the true literals of TERMS under ENV."
  (name-cost terms env))

(defun unit-terms (literals)
  (mapcar (lambda (l) (cons 1 l)) literals))

(defun aux-count (cnf)
  (count-if (lambda (i) (cnf-aux-variable-p cnf i))
            (loop for i from 1 to (cnf-variable-count cnf) collect i)))

(defun binomial (n k)
  "C(N, K)."
  (if (<= 0 k n)
      (let ((r 1))
        (loop for i from 1 to k do (setf r (/ (* r (- n (1- i))) i)))
        r)
      0))

;;; ------------------------------------------------------------ construction

(deftest-parametrize cardinality-folding
    ((form expected)
     :ids ("amk-negative" "amk-trivial" "amk-zero" "amk-zero-one" "amk-n-1" "amo-two"
           "amo-three" "amk-true-operand" "amk-false-operand" "amk-true-overflow"
           "alk-one" "alk-zero" "alk-too-many" "alk-all" "alk-two-of-four"
           "eo-one" "eo-none" "eo-two" "eo-three" "pb-weight-zero" "pb-not-all"
           "pb-node" "pb-true-operand" "amo-duplicate")
     ((sat-at-most-k '("a" "b") -1) :false)
     ((sat-at-most-k '("a" "b") 2) :true)
     ((sat-at-most-k '("a" "b" "c") 0) '(:and (:not "a") (:not "b") (:not "c")))
     ((sat-at-most-k '("a") 0) '(:not "a"))
     ((sat-at-most-k '("a" "b" "c") 2) '(:or (:not "a") (:not "b") (:not "c")))
     ((sat-at-most-one '("a" "b")) '(:or (:not "a") (:not "b")))
     ((sat-at-most-one '("a" "b" "c")) '(:at-most 1 "a" "b" "c"))
     ((sat-at-most-k (list (sat-true) "a" "b" "c") 2) '(:at-most 1 "a" "b" "c"))
     ((sat-at-most-k (list (sat-false) "a" "b") 1) '(:or (:not "a") (:not "b")))
     ((sat-at-most-k (list (sat-true) (sat-true) "a") 1) :false)
     ((sat-at-least-k '("a" "b" "c") 1) '(:or "a" "b" "c"))
     ((sat-at-least-k '("a" "b" "c") 0) :true)
     ((sat-at-least-k '("a" "b") 3) :false)
     ((sat-at-least-k '("a" "b" "c") 3) '(:and "a" "b" "c"))
     ((sat-at-least-k '("a" "b" "c" "d") 2) '(:at-most 2 (:not "a") (:not "b") (:not "c") (:not "d")))
     ((sat-exactly-one '("a")) "a")
     ((sat-exactly-one '()) :false)
     ((sat-exactly-one '("a" "b")) '(:and (:or (:not "a") (:not "b")) (:or "a" "b")))
     ((sat-exactly-one '("a" "b" "c")) '(:and (:at-most 1 "a" "b" "c") (:or "a" "b" "c")))
     ((sat-pb-at-most '((0 . "a") (2 . "b")) 1) '(:not "b"))
     ((sat-pb-at-most '((2 . "a") (3 . "b")) 4) '(:or (:not "a") (:not "b")))
     ((sat-pb-at-most '((2 . "a") (3 . "b") (4 . "c")) 5) '(:pb-at-most 5 (2 "a") (3 "b") (4 "c")))
     ((sat-pb-at-most (list (cons 3 (sat-true)) '(2 . "a") '(2 . "b")) 4) '(:pb-at-most 1 (2 "a") (2 "b")))
     ((sat-at-most-one '("a" "a")) '(:or (:not "a") (:not "a"))))
  (ok (equal expected (sx form))))

(deftest-parametrize cardinality-auto-encoding
    ((form expected)
     :ids ("amo-3" "amo-6" "amo-7" "amk-2" "amk-3-of-9" "pb" "explicit-kept" "explicit-pairwise")
     ((sat-at-most-one (vnames 3)) :pairwise)
     ((sat-at-most-one (vnames 6)) :pairwise)
     ((sat-at-most-one (vnames 7)) :sequential)
     ((sat-at-most-k (vnames 4) 2) :totalizer)
     ((sat-at-most-k (vnames 9) 3) :totalizer)
     ((sat-pb-at-most (mapcar (lambda (n w) (cons w n)) (vnames 3) '(1 2 3)) 3) :bdd)
     ((sat-at-most-one (vnames 3) :encoding :sequential) :sequential)
     ((sat-at-most-k (vnames 8) 3 :encoding :pairwise) :pairwise))
  (ok (eq :at-most (formula-operator form)))
  (ok (eq expected (formula-encoding form))))

(deftest cardinality-node-readers
  (let ((node (sat-pb-at-most (list (cons 2 "a") (cons 3 (sat-not (sat-var "b"))) (cons 4 "c")) 5
                              :encoding :totalizer)))
    (ok (eq :at-most (formula-operator node)))
    (ok (equal '("a" (:not "b") "c") (mapcar #'sx (formula-operands node))) "literal formulas")
    (ok (every #'literal-p (formula-operands node)))
    (ok (equal '(2 3 4) (formula-weights node)))
    (ok (eql 5 (formula-bound node)))
    (ok (eq :totalizer (formula-encoding node)))
    (ok (equal '("a" "b" "c") (formula-variables node))))
  (let ((v (sat-var "a")))
    (ok (null (formula-bound v)) "NIL for other operators")
    (ok (null (formula-weights v)))
    (ok (null (formula-encoding v)))))

(deftest cardinality-argument-errors
  (ok (signals (sat-at-most-k '("a" "b") "2") 'type-error))
  (ok (signals (sat-at-most-k '("a" "b") 1.5) 'type-error))
  (ok (signals (sat-pb-at-most '((-1 . "a") (1 . "b")) 1) 'type-error))
  (ok (signals (sat-pb-at-most '((1/2 . "a") (1 . "b")) 1) 'type-error))
  (ok (signals (sat-pb-at-most '("a" (1 . "b")) 1) 'type-error) "a term that is not a cons")
  (ok (signals (sat-at-most-one '("a" "b" "c") :encoding :ladder) 'type-error))
  (ok (signals (sat-at-most-k '("a") 5 :encoding :ladder) 'type-error) "checked before folding")
  (ok (signals (sat-at-most-one (list "a" (f '(:and "b" "c")))) 'sat-invalid-formula))
  (ok (signals (sat-at-least-k (list "a" nil) 1) 'sat-invalid-formula))
  (ok (equal '(:at-most 1 "a" "z" "c")
             (sx (handler-bind ((sat-invalid-formula (lambda (c) (use-value "z" c))))
                   (sat-at-most-one (list "a" (f '(:or "b" "d")) "c")))))
      "USE-VALUE replaces the element"))

;;; -------------------------------------------------- eval, sexp, assign

(deftest cardinality-eval
  (let ((rng (make-rng 211)))
    (dotimes (i 120)
      (let* ((names (vnames (1+ (rng-int rng 5))))
             (terms (mapcar (lambda (l) (cons (rng-int rng 4) l)) (random-literals rng names)))
             (k (- (rng-int rng 8) 1))
             (node (sat-pb-at-most terms k))
             (env (nth (rng-int rng (expt 2 (length names))) (all-assignments names))))
        (ok (eq (<= (weighted terms env) k) (formula-eval node env))
            (format nil "case ~D" i))))
    (let ((node (sat-at-most-one '("a" "b" "c"))))
      (ok (formula-eval node '(("a" . t) ("b" . nil) ("c" . nil))))
      (ok (not (formula-eval node '(("a" . t) ("b" . nil) ("c" . t)))))
      (ok (formula-eval (sat-not node) '(("a" . t) ("b" . t) ("c" . nil))))
      (ok (signals (formula-eval node '(("a" . t))) 'sat-unbound-variable)))))

(deftest cardinality-sexp
  (ok (equal '(:at-most 1 "a" "b" "c") (sx (sat-at-most-one '("a" "b" "c")))))
  (ok (equal '(:pb-at-most 5 (2 "a") (3 (:not "b")) (4 "c"))
             (sx (sat-pb-at-most (list (cons 2 "a") (cons 3 (sat-not (sat-var "b"))) (cons 4 "c")) 5))))
  (ok (equal '(:at-most 2 (:var :k1) (:var :k2) (:var :k3) "d")
             (sx (sat-at-most-k '(:k1 :k2 :k3 "d") 2)))
      "keyword names as (:var NAME)")
  (dolist (s '((:at-most 1 "a" "b" "c")
               (:at-most 2 "a" (:not "b") "c" "d")
               (:pb-at-most 5 (2 "a") (3 (:not "b")) (4 "c"))
               (:or (:at-most 1 "a" "b" "c") (:not (:pb-at-most 3 (2 "a") (2 "d") (3 "e"))))))
    (ok (equal s (fsx s)) (format nil "round trip ~S" s)))
  (ok (eq :true (fsx '(:at-most 3 "a" "b"))) "folded on reading")
  (ok (equal '(:not "b") (fsx '(:pb-at-most 1 (0 "a") (2 "b")))))
  (ok (equal '(:at-most 1 "b" "c" "d") (fsx '(:at-most 2 :true "b" "c" "d"))))
  (ok (eq :totalizer (formula-encoding (sexp->formula '(:at-most 2 "a" "b" "c" "d"))))
      ":AUTO on reading")
  (dolist (bad '((:at-most "1" "a" "b") (:at-most 1.0 "a" "b") (:at-most)
                 (:at-most 1 (:and "a" "b") "c") (:at-most 1 nil "b")
                 (:pb-at-most 1 ("w" "a") (1 "b")) (:pb-at-most 1 (-1 "a") (1 "b"))
                 (:pb-at-most 1 (1 "a" "b")) (:pb-at-most 1 "a")))
    (ok (signals (sexp->formula bad) 'sat-invalid-formula) (format nil "malformed ~S" bad)))
  (ok (search "AT-MOST" (string-upcase (princ-to-string (sat-at-most-one '("a" "b" "c")))))
      "PRINT-OBJECT shows the sexp"))

(deftest cardinality-assign
  (let ((amo (sat-at-most-one '("a" "b" "c"))))
    (ok (equal '(:and (:not "b") (:not "c")) (sx (formula-assign amo "a" t))))
    (ok (equal '(:or (:not "b") (:not "c")) (sx (formula-assign amo "a" nil))))
    (ok (equal '(:at-most 1 "a" "b" "c") (sx (formula-assign amo "z" t))) "other names")
    (ok (eq :true (fsx (sx (formula-assign (formula-assign amo "a" nil) "b" nil))))))
  (let ((node (formula-assign (sat-at-most-k '("a" "b" "c" "d" "e") 2 :encoding :sequential) "a" nil)))
    (ok (equal '(:at-most 2 "b" "c" "d" "e") (sx node)))
    (ok (eq :sequential (formula-encoding node)) "the encoding is kept"))
  (ok (equal '(:pb-at-most 2 (3 "b") (1 "c"))
             (sx (formula-assign (sat-pb-at-most '((2 . "a") (3 . "b") (1 . "c")) 4) "a" t)))))

;;; ------------------------------------------- encodings vs brute force

(deftest-parametrize encodings-cardinality-brute-force
    ((encoding)
     :ids ("auto" "pairwise" "sequential" "totalizer" "bdd")
     (:auto) (:pairwise) (:sequential) (:totalizer) (:bdd))
  (let ((rng (make-rng 223)))
    (loop for n from 1 to 5
          for names = (vnames n)
          do (loop for k from -1 to (1+ n)
                   do (let ((lits (random-literals rng names)))
                        (flet ((card (predicate) (lambda (env) (funcall predicate (weighted (unit-terms lits) env)))))
                          (ok (equal (brute-keys names (card (lambda (s) (<= s k))))
                                     (projected-keys (sat-at-most-k lits k :encoding encoding) names))
                              (format nil "at most ~D of ~S" k (mapcar #'sx lits)))
                          (ok (equal (brute-keys names (card (lambda (s) (>= s k))))
                                     (projected-keys (sat-at-least-k lits k :encoding encoding) names))
                              (format nil "at least ~D of ~S" k (mapcar #'sx lits))))))
             (let ((lits (random-literals rng names)))
               (flet ((card (predicate) (lambda (env) (funcall predicate (weighted (unit-terms lits) env)))))
                 (ok (equal (brute-keys names (card (lambda (s) (<= s 1))))
                            (projected-keys (sat-at-most-one lits :encoding encoding) names))
                     (format nil "at most one of ~S" (mapcar #'sx lits)))
                 (ok (equal (brute-keys names (card (lambda (s) (= s 1))))
                            (projected-keys (sat-exactly-one lits :encoding encoding) names))
                     (format nil "exactly one of ~S" (mapcar #'sx lits))))))))

(deftest-parametrize encodings-pb-brute-force
    ((encoding)
     :ids ("auto" "pairwise" "sequential" "totalizer" "bdd")
     (:auto) (:pairwise) (:sequential) (:totalizer) (:bdd))
  (let ((rng (make-rng 227)))
    (dotimes (i 30)
      (let* ((names (vnames (1+ (rng-int rng 5))))
             (terms (mapcar (lambda (l) (cons (rng-int rng 5) l)) (random-literals rng names)))
             (total (reduce #'+ terms :key #'car))
             (k (- (rng-int rng (+ total 3)) 1)))
        (ok (equal (brute-keys names (lambda (env) (<= (weighted terms env) k)))
                   (projected-keys (sat-pb-at-most terms k :encoding encoding) names))
            (format nil "case ~D: ~S <= ~D" i (mapcar (lambda (e) (list (car e) (sx (cdr e)))) terms) k))))))

(deftest-parametrize encodings-size
    ((encoding)
     :ids ("pairwise" "sequential" "totalizer" "bdd")
     (:pairwise) (:sequential) (:totalizer) (:bdd))
  ;; Top-level nodes over fresh variables: :PAIRWISE adds no auxiliary and,
  ;; for unit weights, exactly C(n, k+1) clauses; the others add at most
  ;; n * (k + 1) auxiliaries.
  (loop for n from 4 to 8
        do (loop for k from 1 to (min 3 (- n 2)) ; k = n-1 folds to one clause
                 do (let* ((node (sat-at-most-k (vnames n) k :encoding encoding))
                           (cnf (to-cnf node)))
                      (ok (eq :at-most (formula-operator node)))
                      (ok (equal (vnames n) (cnf-user-variables cnf)) "user variables first")
                      (if (eq encoding :pairwise)
                          (progn
                            (ok (zerop (aux-count cnf)) (format nil "n=~D k=~D: no auxiliary" n k))
                            (ok (= (binomial n (1+ k)) (cnf-clause-count cnf))
                                (format nil "n=~D k=~D: C(n, k+1) clauses" n k)))
                          (ok (<= (aux-count cnf) (* n (1+ k)))
                              (format nil "n=~D k=~D: ~D auxiliaries" n k (aux-count cnf))))))))

(deftest-parametrize encodings-nested
    ((encoding)
     :ids ("auto" "pairwise" "sequential" "totalizer" "bdd")
     (:auto) (:pairwise) (:sequential) (:totalizer) (:bdd))
  ;; Constraints under :NOT, :OR, :IMPLIES and :IFF (both polarities):
  ;; projected models against truth tables.
  (let ((rng (make-rng 229)) (names (vnames 4)))
    (labels ((node ()
               (let* ((lits (loop repeat (+ 2 (rng-int rng 3)) collect (random-literal rng names)))
                      (terms (mapcar (lambda (l) (cons (1+ (rng-int rng 3)) l)) lits))
                      (k (rng-int rng (reduce #'+ terms :key #'car))))
                 (if (zerop (rng-int rng 2))
                     (cons (sat-at-most-k lits k :encoding encoding)
                           (lambda (env) (<= (weighted (unit-terms lits) env) k)))
                     (cons (sat-pb-at-most terms k :encoding encoding)
                           (lambda (env) (<= (weighted terms env) k))))))
             (term (depth)
               (if (or (zerop depth) (zerop (rng-int rng 3)))
                   (node)
                   (let ((a (term (1- depth))) (b (term (1- depth))))
                     (ecase (rng-int rng 4)
                       (0 (cons (sat-not (car a)) (lambda (env) (not (funcall (cdr a) env)))))
                       (1 (cons (sat-or (car a) (car b))
                                (lambda (env) (or (funcall (cdr a) env) (funcall (cdr b) env)))))
                       (2 (cons (sat-implies (car a) (car b))
                                (lambda (env) (or (not (funcall (cdr a) env)) (funcall (cdr b) env)))))
                       (3 (cons (sat-iff (car a) (car b))
                                (lambda (env) (eq (not (funcall (cdr a) env))
                                                  (not (funcall (cdr b) env)))))))))))
      (dotimes (i 25)
        (destructuring-bind (formula . predicate) (term 2)
          (ok (equal (brute-keys names predicate) (projected-keys formula names))
              (format nil "formula ~D: ~S" i (sx formula))))))))

(deftest to-cnf-node-is-cnf-add
  ;; TO-CNF of a top-level node adds exactly what CNF-ADD-PB-AT-MOST adds.
  (dolist (encoding '(:pairwise :sequential :totalizer :bdd))
    (let* ((terms (list (cons 1 "a") (cons 2 (sat-not (sat-var "b"))) (cons 1 "c") (cons 3 "d")))
           (node (sat-pb-at-most terms 3 :encoding encoding))
           (from-formula (to-cnf node))
           (direct (make-cnf)))
      (dolist (name '("a" "b" "c" "d")) (cnf-ensure-variable direct name))
      (cnf-add-pb-at-most direct (list (cons 1 1) (cons 2 -2) (cons 1 3) (cons 3 4)) 3
                          :encoding encoding)
      (ok (equal (cnf-clauses direct) (cnf-clauses from-formula)) (format nil "~A clauses" encoding))
      (ok (= (cnf-variable-count direct) (cnf-variable-count from-formula))))))

;;; ------------------------------------------------------------ CNF level

(defun int-keys (cnf n)
  (sort (mapcar (lambda (m) (format nil "~{~:[0~;1~]~}" (mapcar #'cdr m)))
                (collect-models (solve-all cnf :project (loop for i from 1 to n collect i))))
        #'string<))

(defun int-brute-keys (clauses n predicate)
  (sort (mapcar (lambda (bits) (format nil "~{~:[0~;1~]~}"
                                       (loop for i from 1 to n collect (= 1 (sbit bits i)))))
                (remove-if-not predicate (brute-models clauses n)))
        #'string<))

(deftest-parametrize cnf-add-brute-force
    ((encoding)
     :ids ("auto" "pairwise" "sequential" "totalizer" "bdd")
     (:auto) (:pairwise) (:sequential) (:totalizer) (:bdd))
  ;; Over a CNF that already has clauses: the models are the old ones that
  ;; satisfy the constraint.
  (let ((rng (make-rng 233)))
    (dotimes (i 30)
      (let* ((n (+ 2 (rng-int rng 4)))
             (base (loop repeat (rng-int rng 3)
                         collect (list (let ((v (1+ (rng-int rng n)))) (if (zerop (rng-int rng 2)) v (- v)))
                                       (let ((v (1+ (rng-int rng n)))) (if (zerop (rng-int rng 2)) v (- v))))))
             (lits (loop for v from 1 to n collect (if (zerop (rng-int rng 2)) v (- v))))
             (terms (mapcar (lambda (l) (cons (rng-int rng 4) l)) lits))
             (k (- (rng-int rng (+ n 3)) 1))
             (count-true (lambda (bits) (count-if (lambda (l) (if (plusp l) (= 1 (sbit bits l)) (= 0 (sbit bits (- l))))) lits)))
             (weight (lambda (bits) (int-cost terms (lambda (v) (= 1 (sbit bits v)))))))
        (flet ((check (what adder predicate)
                 (let* ((cnf (clauses->cnf base n))
                        (returned (funcall adder cnf)))
                   (ok (eq cnf returned) "returns the CNF")
                   (ok (equal (int-brute-keys base n predicate) (int-keys cnf n))
                       (format nil "case ~D ~A ~S k=~D base ~S" i what lits k base)))))
          (check "at-most-k" (lambda (c) (cnf-add-at-most-k c lits k :encoding encoding))
                 (lambda (b) (<= (funcall count-true b) k)))
          (check "at-least-k" (lambda (c) (cnf-add-at-least-k c lits k :encoding encoding))
                 (lambda (b) (>= (funcall count-true b) k)))
          (check "at-most-one" (lambda (c) (cnf-add-at-most-one c lits :encoding encoding))
                 (lambda (b) (<= (funcall count-true b) 1)))
          (check "exactly-one" (lambda (c) (cnf-add-exactly-one c lits :encoding encoding))
                 (lambda (b) (= (funcall count-true b) 1)))
          (check "pb-at-most" (lambda (c) (cnf-add-pb-at-most c terms k :encoding encoding))
                 (lambda (b) (<= (funcall weight b) k))))))))

(deftest cnf-add-folding
  (flet ((fresh (n) (clauses->cnf nil n)))
    (let ((cnf (fresh 2)))
      (cnf-add-at-most-k cnf '(1 2) -1)
      (ok (equal '(()) (cnf-clauses cnf)) "K < 0: the empty clause"))
    (let ((cnf (fresh 2)))
      (cnf-add-at-most-k cnf '(1 -2) 2)
      (ok (and (zerop (cnf-clause-count cnf)) (= 2 (cnf-variable-count cnf))) "W <= K: nothing"))
    (let ((cnf (fresh 2)))
      (cnf-add-at-most-k cnf '(1 -2) 0)
      (ok (equal '((-1) (2)) (cnf-clauses cnf)) "K = 0: unit clauses"))
    (let ((cnf (fresh 3)))
      (cnf-add-at-most-k cnf '(1 -2 3) 2)
      (ok (equal '((-1 2 -3)) (cnf-clauses cnf)) "K = W - 1: one clause"))
    (let ((cnf (fresh 2)))
      (cnf-add-pb-at-most cnf '((0 . 1) (2 . 2)) 1)
      (ok (equal '((-2)) (cnf-clauses cnf)) "weight 0 dropped"))
    (let ((cnf (fresh 2)))
      (cnf-add-exactly-one cnf '())
      (ok (equal '(()) (cnf-clauses cnf)) "exactly one of nothing"))
    (let ((cnf (fresh 3)))
      (cnf-add-at-least-k cnf '(1 2 3) 1)
      (ok (equal '((1 2 3)) (cnf-clauses cnf)) "at least one: the clause"))))

(deftest cnf-add-errors
  (let ((cnf (clauses->cnf '((1 2)) 2)))
    (ok (signals (cnf-add-at-most-one cnf '(1 0)) 'sat-invalid-formula))
    (ok (signals (cnf-add-at-most-one cnf '(1 3)) 'sat-invalid-formula) "beyond the variable count")
    (ok (signals (cnf-add-at-most-k cnf '(1 "a") 1) 'sat-invalid-formula))
    (ok (eql 3 (handler-case (cnf-add-exactly-one cnf '(1 -2 3))
                 (sat-invalid-formula (c) (sat-invalid-formula-datum c)))))
    (ok (signals (cnf-add-pb-at-most cnf '((1 . 1) (-2 . 2)) 1) 'type-error))
    (ok (signals (cnf-add-at-most-k cnf '(1 2) 'one) 'type-error))
    (ok (signals (cnf-add-at-least-k cnf '(1 2) 1 :encoding :ladder) 'type-error))
    (ok (equal '((1 2)) (cnf-clauses cnf)) "nothing added")
    (ok (= 2 (cnf-variable-count cnf)) "no auxiliary allocated")))

;;; ------------------------------------------------------- in UNSAT-CORE

(deftest-parametrize cardinality-guarded-in-unsat-core
    ((encoding)
     :ids ("pairwise" "sequential" "totalizer" "bdd")
     (:pairwise) (:sequential) (:totalizer) (:bdd))
  ;; A :NAMED constraint holds only when its selector is assumed.
  (let ((amo (sat-at-most-one '("a" "b" "c") :encoding encoding)))
    (multiple-value-bind (core unsat)
        (unsat-core (sat-true) :named (list (cons "amo" amo) (cons "a" (f "a"))
                                            (cons "b" (f "b")) (cons "c" (f "c"))))
      (ok (eq t unsat))
      (ok (equal '("amo" "b" "c") core) "deletion keeps the constraint and two literals"))
    (multiple-value-bind (core unsat)
        (unsat-core (f '(:and "a" "b")) :named (list (cons "amo" amo) (cons "c" (f "c"))))
      (ok (eq t unsat))
      (ok (equal '("amo") core) "with its selector free, the constraint imposes nothing"))))
