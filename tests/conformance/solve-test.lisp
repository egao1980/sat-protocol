(in-package #:sat-protocol/conformance)

;;; solve: status, models, assumptions, :order / :phase / :complete.

(defun last-name (names) (car (last names)))

(deftest solve-trivial
  (multiple-value-bind (model sat) (solve (f "a"))
    (ok (eq t sat))
    (ok (equal '(("a" . t)) model))))

(deftest solve-unsat
  (multiple-value-bind (model sat) (solve (f '(:and "a" (:not "a"))))
    (ok (null model))
    (ok (null sat))))

(deftest solve-constants
  (multiple-value-bind (model sat) (solve (sat-true))
    (ok (null model))
    (ok (eq t sat) "satisfiable with nothing to bind"))
  (multiple-value-bind (model sat) (solve (sat-false))
    (ok (null model))
    (ok (null sat))))

(deftest solve-complete-model
  (let ((formula (f '(:or "a" "b" "c"))))
    (multiple-value-bind (model sat) (solve formula)
      (ok sat)
      (ok (equal '("a" "b" "c") (mapcar #'car model)) "every variable, index order")
      (ok (every (lambda (pair) (member (cdr pair) '(t nil))) model))
      (ok (formula-eval formula model)))))

(deftest solve-order-decides-hook-choice
  (let ((calls nil))
    (multiple-value-bind (model sat)
        (solve (f '(:or "a" "b" "c"))
               :order (lambda (names) (push names calls) (last-name names))
               :phase :true :complete nil)
      (ok sat)
      (ok (equal '(("c" . t)) model) "one decision satisfies the clause; nothing else assigned")
      (ok (equal '(("a" "b" "c")) calls) "the hook saw the candidates in index order, once"))))

(deftest solve-phase-false
  (multiple-value-bind (model sat)
      (solve (f '(:or "a" "b" "c")) :order #'last-name :phase :false :complete nil)
    (ok sat)
    (ok (= 3 (length model)))
    (ok (equal '(nil t) (multiple-value-list (model-value model "c"))))
    (ok (equal '(nil t) (multiple-value-list (model-value model "b"))))
    (ok (equal '(t t) (multiple-value-list (model-value model "a"))))))

(deftest solve-phase-function
  (multiple-value-bind (model sat)
      (solve (f '(:or "a" "b" "c")) :order #'last-name
             :phase (lambda (name) (string= name "b")) :complete nil)
    (ok sat)
    (ok (equal '(("b" . t) ("c" . nil)) model))))

(deftest solve-complete-fills-with-phase
  (let ((m (solve (f '(:or "a" "b" "c")) :order #'last-name :phase :true)))
    (ok (equal '(("a" . t) ("b" . t) ("c" . t)) m) ":complete t fills unassigned with :true"))
  (let ((m (solve (f '(:or "a" "b" "c")) :order #'last-name
                  :phase (lambda (name) (string= name "c")))))
    (ok (equal '(("a" . nil) ("b" . nil) ("c" . t)) m))))

(deftest solve-order-invalid-choice
  (ok (signals (solve (f '(:or "a" "b")) :order (lambda (names) (declare (ignore names)) "zzz"))
               'sat-error)))

(deftest solve-order-never-sees-auxiliaries
  (let* ((sexp '(:or (:and "a" "b") (:and "c" (:not "d")) (:iff "a" "d")))
         (seen nil))
    (multiple-value-bind (model sat)
        (solve (f sexp) :order (lambda (names) (setf seen (append names seen)) (first names)))
      (ok sat)
      (ok (sexp-eval sexp model))
      (ok (every (lambda (n) (member n '("a" "b" "c" "d") :test #'equal)) seen)))))

(deftest solve-assumptions
  (let ((formula (f '(:or "a" "b"))))
    (let ((m (solve formula :assumptions (list (sat-not (sat-var "a"))))))
      (ok (equal '(nil t) (multiple-value-list (model-value m "a"))))
      (ok (equal '(t t) (multiple-value-list (model-value m "b")))))
    (ok (null (nth-value 1 (solve (f '(:not "b")) :assumptions '("b"))))
        "a bare name is the positive literal")
    (ok (null (nth-value 1 (solve formula :assumptions (list (sat-not (sat-var "a"))
                                                             (sat-not (sat-var "b")))))))))

(deftest solve-assumption-on-new-variable
  (let ((m (solve (f "a") :assumptions '("z"))))
    (ok (equal '(("a" . t) ("z" . t)) m) "new variables follow the formula's, index order")))

(deftest solve-cnf-input-unchanged
  (let ((cnf (clauses->cnf '((1 2) (-1 2)) 2)))
    (multiple-value-bind (model sat) (solve cnf :assumptions '(3))
      (ok sat)
      (ok (equal '(t t) (multiple-value-list (model-value model 2))))
      (ok (equal '(t t) (multiple-value-list (model-value model 3)))))
    (ok (= 2 (cnf-variable-count cnf)) "the given CNF is not modified")
    (ok (equal '((1 2) (-1 2)) (cnf-clauses cnf)))))

(deftest solve-hides-auxiliaries
  (let ((sexp '(:or (:and "a" "b") (:and "c" "d"))))
    (multiple-value-bind (model sat) (solve (f sexp))
      (ok sat)
      (ok (equal '("a" "b" "c" "d") (mapcar #'car model)))
      (ok (sexp-eval sexp model)))))

(deftest-parametrize solve-pigeonhole
    ((pigeons holes satisfiable)
     :ids ("2-2" "3-2" "3-3" "4-3" "4-4")
     (2 2 t) (3 2 nil) (3 3 t) (4 3 nil) (4 4 t))
  (multiple-value-bind (clauses n) (pigeonhole pigeons holes)
    (multiple-value-bind (model sat) (solve (clauses->cnf clauses n))
      (ok (eq satisfiable sat))
      (when sat
        (ok (clauses-satisfied-p clauses (model->assignment model)))))))

(deftest-parametrize solve-dimacs-fixtures
    ((file satisfiable)
     :ids ("tiny-sat" "tiny-unsat" "satlib-style" "php-4-3" "rand-sat" "rand-unsat")
     ("tiny-sat.cnf" t) ("tiny-unsat.cnf" nil) ("satlib-style.cnf" t)
     ("php-4-3.cnf" nil) ("rand3-20-91-sat.cnf" t) ("rand3-20-91-unsat.cnf" nil))
  (let ((cnf (read-dimacs (fixture-path file))))
    (multiple-value-bind (model sat) (solve cnf)
      (ok (eq satisfiable sat))
      (when sat
        (ok (clauses-satisfied-p (cnf-clauses cnf) (model->assignment model)))))))

(deftest solve-random-3sat-property
  ;; Near the threshold (ratio 4.3): status against brute force, models by evaluation.
  (let ((rng (make-rng 2026)) (sat-count 0) (unsat-count 0))
    (dotimes (i 40)
      (let* ((clauses (random-3sat rng 10 43)))
        (multiple-value-bind (model sat) (solve (clauses->cnf clauses 10))
          (ok (eq (brute-satisfiable-p clauses 10) sat) (format nil "instance ~D status" i))
          (if sat
              (progn (incf sat-count)
                     (ok (clauses-satisfied-p clauses (model->assignment model))
                         (format nil "instance ~D model" i)))
              (incf unsat-count)))))
    (ok (and (plusp sat-count) (plusp unsat-count)) "both outcomes exercised")))

(deftest solve-random-formulas
  ;; Non-clausal formulas (the Tseitin path): status against truth tables.
  (let ((rng (make-rng 7)) (names '("p" "q" "r" "s" "t")))
    (dotimes (i 40)
      (let* ((sexp (random-sexp rng names 4))
             (vars (sexp-vars sexp))
             (expected (some (lambda (env) (sexp-eval sexp env)) (all-assignments vars))))
        (multiple-value-bind (model sat) (solve (f sexp))
          (ok (eq (and expected t) sat) (format nil "formula ~D status" i))
          (when sat
            (ok (sexp-eval sexp model) (format nil "formula ~D model" i))))))))
