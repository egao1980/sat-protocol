(in-package #:sat-protocol/tests)

;;; Constructors, constant folding, variables, evaluation, sexps.

(deftest constants
  (ok (eq :true (formula-operator (sat-true))))
  (ok (eq :false (formula-operator (sat-false))))
  (ok (formula-p (sat-true)))
  (ok (not (formula-p :true)))
  (ok (eq :true (sx (sat-true))))
  (ok (eq :false (sx (sat-false)))))

(deftest variables
  (let ((v (sat-var "x")))
    (ok (eq :var (formula-operator v)))
    (ok (equal "x" (sat-var-name v)))
    (ok (null (formula-operands v)))
    (ok (equal 7 (sat-var-name (sat-var 7))))
    (ok (equal '(pkg "1.0") (sat-var-name (sat-var '(pkg "1.0")))) "any EQUAL-comparable name")))

(deftest sat-var-nil-name
  (ok (signals (sat-var nil) 'sat-invalid-formula))
  (ok (equal "y" (handler-bind ((sat-invalid-formula (lambda (c) (use-value "y" c))))
                   (sat-var-name (sat-var nil))))
      "USE-VALUE supplies a replacement name"))

(deftest-parametrize folding
    ((input expected)
     :ids ("not-true" "not-false" "double-not" "and-empty" "and-one" "and-true" "and-false"
           "and-flatten" "and-keeps-duplicates" "or-empty" "or-one" "or-false" "or-true"
           "or-flatten" "implies-false-p" "implies-true-p" "implies-true-q" "implies-false-q"
           "implies" "iff-true-p" "iff-false-p" "iff-true-q" "iff-false-q" "iff"
           "nested-collapse" "not-and-kept")
     ('(:not :true) :false)
     ('(:not :false) :true)
     ('(:not (:not "a")) "a")
     ('(:and) :true)
     ('(:and "a") "a")
     ('(:and :true "a" :true "b") '(:and "a" "b"))
     ('(:and "a" :false "b") :false)
     ('(:and "a" (:and "b" "c") "d") '(:and "a" "b" "c" "d"))
     ('(:and "a" "a") '(:and "a" "a"))
     ('(:or) :false)
     ('(:or "a") "a")
     ('(:or :false "a" "b") '(:or "a" "b"))
     ('(:or "a" :true) :true)
     ('(:or (:or "a" "b") "c") '(:or "a" "b" "c"))
     ('(:implies :false "q") :true)
     ('(:implies :true "q") "q")
     ('(:implies "p" :true) :true)
     ('(:implies "p" :false) '(:not "p"))
     ('(:implies "p" "q") '(:implies "p" "q"))
     ('(:iff :true "q") "q")
     ('(:iff :false "q") '(:not "q"))
     ('(:iff "p" :true) "p")
     ('(:iff "p" :false) '(:not "p"))
     ('(:iff "p" "q") '(:iff "p" "q"))
     ('(:and (:or :false (:and :true "a")) (:not (:not :true))) "a")
     ('(:not (:and "a" "b")) '(:not (:and "a" "b"))))
  (ok (equal expected (fsx input))))

(deftest constructors-match-sexp
  (ok (equal '(:and "a" "b" "c") (sx (sat-and (sat-var "a") (sat-and (sat-var "b") (sat-var "c"))))))
  (ok (equal '(:or "a" "b") (sx (sat-or* (list (sat-var "a") (sat-false) (sat-var "b"))))))
  (ok (equal :true (sx (sat-and* nil))))
  (ok (equal '(:implies "p" (:or "q" "r"))
             (sx (sat-implies (sat-var "p") (sat-or (sat-var "q") (sat-var "r"))))))
  (ok (equal '(:iff "p" "q") (sx (sat-iff (sat-var "p") (sat-var "q")))))
  (ok (equal '(:or "a" "b") (formula->sexp (sat-or (sat-var "a") (sat-var "b"))))))

(deftest operands
  (let ((a (sat-var "a")) (b (sat-var "b")))
    (ok (equal (list a b) (formula-operands (sat-and a b))))
    (ok (equal (list a) (formula-operands (sat-not a))))
    (ok (equal (list a b) (formula-operands (sat-implies a b))))
    (ok (eq :iff (formula-operator (sat-iff a b))))))

(deftest invalid-operands
  (ok (signals (sat-and (sat-var "a") 42) 'sat-invalid-formula))
  (ok (signals (sat-not "a") 'sat-invalid-formula))
  (ok (signals (sat-implies t (sat-var "a")) 'sat-error))
  (ok (eql 42 (handler-case (sat-or 42)
                (sat-invalid-formula (c) (sat-invalid-formula-datum c)))))
  (ok (equal '(:and "a" "b")
             (handler-bind ((sat-invalid-formula (lambda (c) (use-value (sat-var "b") c))))
               (sx (sat-and (sat-var "a") :oops))))
      "USE-VALUE replaces the operand"))

(deftest literals
  (let ((a (sat-var "a")))
    (ok (literal-p a))
    (ok (literal-p (sat-not a)))
    (ok (not (literal-p (sat-not (sat-and a (sat-var "b"))))))
    (ok (not (literal-p (sat-true))))
    (ok (equal "a" (literal-name (sat-not a))))
    (ok (equal "a" (literal-name "a")) "a bare name")
    (ok (literal-positive-p a))
    (ok (not (literal-positive-p (sat-not a))))
    (ok (literal-positive-p "a"))))

(deftest formula-variables-order
  (ok (equal '("b" "a" "c")
             (formula-variables (f '(:or (:and "b" "a") (:implies "a" "c") (:not "b"))))))
  (ok (null (formula-variables (sat-true))))
  (ok (equal '(1 2) (formula-variables (f '(:iff 1 (:var 2)))))))

(deftest formula-eval-assignments
  (let ((formula (f '(:and (:or "a" "b") (:implies "a" "c")))))
    (ok (formula-eval formula '(("a" . t) ("b" . nil) ("c" . t))))
    (ok (not (formula-eval formula '(("a" . t) ("b" . nil) ("c" . nil)))))
    (let ((table (make-hash-table :test 'equal)))
      (setf (gethash "a" table) nil (gethash "b" table) t (gethash "c" table) nil)
      (ok (formula-eval formula table) "hash table"))
    (ok (formula-eval formula (lambda (name) (values (string= name "b") t))) "function")
    (ok (eq t (formula-eval (sat-true) nil)))
    (ok (eq nil (formula-eval (sat-false) nil)))))

(deftest formula-eval-unbound
  (let ((formula (f '(:and "a" "b"))))
    (ok (signals (formula-eval formula '(("a" . t))) 'sat-unbound-variable))
    (ok (equal "b" (handler-case (formula-eval formula '(("a" . t)))
                     (sat-unbound-variable (c) (sat-unbound-variable-name c)))))
    (ok (eq t (handler-bind ((sat-unbound-variable (lambda (c) (use-value t c))))
                (formula-eval formula '(("a" . t))))))
    (ok (eq nil (formula-eval formula '(("a" . t)) :default nil)))
    (ok (eq t (formula-eval formula '(("a" . t)) :default t)))))

(deftest formula-eval-truth-tables
  (let ((rng (make-rng 3)) (names '("a" "b" "c" "d")))
    (dotimes (i 50)
      (let* ((sexp (random-sexp rng names 4))
             (formula (f sexp)))
        (ok (every (lambda (env) (eq (and (sexp-eval sexp env) t) (formula-eval formula env :default nil)))
                   (all-assignments names))
            (format nil "formula ~D" i))))))

(deftest formula-assign-folds
  (let ((formula (f '(:and (:or "x" "y") (:implies "x" "z")))))
    (ok (equal '(:and (:or "x" "y") (:implies "x" "z")) (sx (formula-assign formula "w" t))))
    (ok (equal "z" (sx (formula-assign formula "x" t))))
    (ok (equal "y" (sx (formula-assign formula "x" nil))))
    (ok (equal :false (sx (formula-assign (formula-assign formula "x" nil) "y" nil))))
    (ok (equal '(:not "q") (sx (formula-assign (f '(:iff "p" "q")) "p" nil))))))

(deftest sexp-round-trip
  (let ((rng (make-rng 17)))
    (dotimes (i 30)
      (let* ((sexp (random-sexp rng '("a" b 3 :k) 3))
             (folded (fsx sexp)))
        (ok (equal folded (fsx folded)) (format nil "round trip ~D" i))
        (ok (every (lambda (env) (eq (and (sexp-eval sexp env) t) (and (sexp-eval folded env) t)))
                   (all-assignments (sexp-vars sexp)))
            "folding preserves meaning")))))

(deftest sexp-names
  (ok (equal "a" (fsx "a")))
  (ok (equal 'foo (fsx 'foo)))
  (ok (equal 12 (fsx 12)))
  (ok (equal '(:var (p 1)) (fsx '(:var (p 1)))) "non-atomic names use :var")
  (ok (equal '(:var :true) (fsx '(:var :true))) ":true as a variable name")
  (ok (equal :true (fsx :true))))

(deftest sexp-invalid
  (ok (signals (sexp->formula '(:nand "a" "b")) 'sat-invalid-formula))
  (ok (signals (sexp->formula '(:not "a" "b")) 'sat-invalid-formula))
  (ok (signals (sexp->formula '(:implies "a")) 'sat-invalid-formula))
  (ok (signals (sexp->formula nil) 'sat-invalid-formula))
  (ok (signals (sexp->formula '("a" "b")) 'sat-invalid-formula))
  (ok (equal '(:and "a" "z")
             (handler-bind ((sat-invalid-formula (lambda (c) (use-value "z" c))))
               (fsx '(:and "a" (:bogus)))))
      "USE-VALUE takes a replacement sexp"))

(deftest print-formula
  (let ((text (prin1-to-string (f '(:and "a" (:not "b"))))))
    (ok (search "FORMULA" (string-upcase text)))
    (ok (search "(:AND \"a\" (:NOT \"b\"))" text))))
