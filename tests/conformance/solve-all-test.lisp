(in-package #:sat-protocol/conformance)

;;; solve-all: exact enumeration, projection, limit, laziness.

(defun model-key (model)
  (format nil "~S" model))

(defun distinct-p (models)
  (= (length models)
     (length (remove-duplicates (mapcar #'model-key models) :test #'string=))))

(deftest-parametrize solve-all-counts
    ((sexp count)
     :ids ("or2" "and2" "iff" "xor" "implies" "or3" "taut" "contradiction" "mutex3")
     ('(:or "a" "b") 3)
     ('(:and "a" "b") 1)
     ('(:iff "a" "b") 2)
     ('(:not (:iff "a" "b")) 2)
     ('(:implies "a" "b") 3)
     ('(:or "a" "b" "c") 7)
     ('(:or "a" (:not "a")) 2)
     ('(:and "a" (:not "a")) 0)
     ('(:and (:or "a" "b" "c") (:not (:and "a" "b")) (:not (:and "a" "c")) (:not (:and "b" "c"))) 3))
  (let* ((models (collect-models (solve-all (f sexp))))
         (vars (sexp-vars sexp)))
    (ok (= count (length models)))
    (ok (distinct-p models))
    (ok (every (lambda (m) (equal vars (mapcar #'car m))) models) "each binds exactly the variables")
    (ok (every (lambda (m) (sexp-eval sexp m)) models))))

(deftest solve-all-project
  (let ((formula (f '(:or "a" "b" "c"))))
    (let ((models (collect-models (solve-all formula :project '("a")))))
      (ok (= 2 (length models)) "a = T and a = F both extend to models")
      (ok (every (lambda (m) (equal '("a") (mapcar #'car m))) models)))
    (let ((models (collect-models (solve-all formula :project '("c" "a")))))
      (ok (= 4 (length models)))
      (ok (every (lambda (m) (equal '("c" "a") (mapcar #'car m))) models) "PROJECT order"))
    (let ((models (collect-models (solve-all (f '(:and "a" "b")) :project '("b")))))
      (ok (equal '((("b" . t))) models)))))

(deftest solve-all-project-free-variable
  (let ((models (collect-models (solve-all (f '(:or "a" "b")) :project '("a" "b" "z")))))
    (ok (= 6 (length models)) "a variable not in the formula is free")
    (ok (distinct-p models))))

(deftest solve-all-limit
  (ok (= 2 (length (collect-models (solve-all (f '(:or "a" "b" "c")) :limit 2)))))
  (ok (null (collect-models (solve-all (f '(:or "a" "b" "c")) :limit 0))))
  (ok (= 7 (length (collect-models (solve-all (f '(:or "a" "b" "c")) :limit 100))))))

(deftest solve-all-next-model
  (let ((seq (solve-all (f '(:and "a" (:not "b"))))))
    (ok (typep seq 'model-sequence))
    (ok (equal '((("a" . t) ("b" . nil)) t) (multiple-value-list (next-model seq))))
    (ok (equal '(nil nil) (multiple-value-list (next-model seq))))
    (ok (equal '(nil nil) (multiple-value-list (next-model seq))) "stays exhausted")
    (ok (null (collect-models seq)))))

(deftest solve-all-unsat
  (ok (null (collect-models (solve-all (f '(:and "a" (:not "a"))))))))

(deftest solve-all-assumptions
  (let ((models (collect-models (solve-all (f '(:or "a" "b"))
                                           :assumptions (list (sat-not (sat-var "a")))))))
    (ok (equal '((("a" . nil) ("b" . t))) models))))

(deftest solve-all-lazy
  ;; 2^20 - 1 models: only the three asked for are searched.
  (let* ((names (loop for i from 1 to 20 collect (format nil "v~D" i)))
         (seq (solve-all (sat-or* (mapcar #'sat-var names)))))
    (let ((first-three (loop repeat 3 collect (next-model seq))))
      (ok (= 3 (length first-three)))
      (ok (distinct-p first-three))
      (ok (every (lambda (m) (= 20 (length m))) first-three)))))

(deftest solve-all-random-against-brute-force
  (let ((rng (make-rng 11)))
    (dotimes (i 15)
      (let* ((clauses (random-3sat rng 8 18))
             (expected (length (brute-models clauses 8)))
             (models (collect-models (solve-all (clauses->cnf clauses 8)))))
        (ok (= expected (length models)) (format nil "instance ~D count" i))
        (ok (distinct-p models))
        (ok (every (lambda (m) (clauses-satisfied-p clauses (model->assignment m))) models))))))
