(in-package #:sat-protocol/conformance)

;;; minimize: weighted preferences against brute force.

(defun objective-cost (objective assignment-fn)
  (loop for (weight . lit) in objective
        sum (if (if (plusp lit) (funcall assignment-fn lit) (not (funcall assignment-fn (- lit))))
                weight 0)))

(deftest minimize-picks-cheapest
  (multiple-value-bind (model cost)
      (minimize (f '(:or "a" "b" "c")) (list (cons 3 "a") (cons 1 "b") (cons 2 "c")))
    (ok (eql 1 cost))
    (ok (equal '(("a" . nil) ("b" . t) ("c" . nil)) model))))

(deftest minimize-preference
  ;; "prefer x true" costs 1 when x is false.
  (multiple-value-bind (model cost)
      (minimize (f '(:implies "x" "y")) (list (cons 1 (sat-not (sat-var "x")))))
    (ok (eql 0 cost))
    (ok (equal '(t t) (multiple-value-list (model-value model "x"))))
    (ok (equal '(t t) (multiple-value-list (model-value model "y"))))))

(deftest minimize-forced-cost
  (multiple-value-bind (model cost)
      (minimize (f '(:and "a" (:or "b" "c"))) (list (cons 5 "a") (cons 2 "b") (cons 2 "c")))
    (ok (eql 7 cost))
    (ok (= 3 (length model)) "complete model")))

(deftest minimize-unsat
  (ok (equal '(nil nil)
             (multiple-value-list (minimize (f '(:and "a" (:not "a"))) (list (cons 1 "a")))))))

(deftest minimize-empty-objective
  (multiple-value-bind (model cost) (minimize (f '(:or "a" "b")) nil)
    (ok (eql 0 cost))
    (ok (sexp-eval '(:or "a" "b") model))))

(deftest minimize-new-variable-in-objective
  (multiple-value-bind (model cost) (minimize (f "a") (list (cons 4 "z")))
    (ok (eql 0 cost))
    (ok (equal '(("a" . t) ("z" . nil)) model))))

(deftest minimize-assumptions
  (multiple-value-bind (model cost)
      (minimize (f '(:or "a" "b")) (list (cons 1 "a") (cons 1 "b")) :assumptions '("a" "b"))
    (ok (eql 2 cost))
    (ok (equal '(("a" . t) ("b" . t)) model))))

(deftest minimize-bad-weight
  (ok (signals (minimize (f "a") (list (cons -1 "a"))) 'type-error))
  (ok (signals (minimize (f "a") (list (cons 1.5 "a"))) 'type-error)))

(deftest minimize-random-against-brute-force
  (let ((rng (make-rng 5)))
    (dotimes (i 15)
      (let* ((clauses (random-3sat rng 8 16))
             (objective (loop repeat 6
                              collect (cons (1+ (rng-int rng 5))
                                            (let ((v (1+ (rng-int rng 8))))
                                              (if (zerop (rng-int rng 2)) v (- v))))))
             (brute (brute-models clauses 8))
             (best (and brute
                        (reduce #'min (mapcar (lambda (bits)
                                                (objective-cost objective
                                                                (lambda (v) (= 1 (sbit bits v)))))
                                              brute))))
             (lit-objective (mapcar (lambda (entry)
                                      (cons (car entry)
                                            (if (plusp (cdr entry))
                                                (sat-var (cdr entry))
                                                (sat-not (sat-var (- (cdr entry)))))))
                                    objective)))
        (multiple-value-bind (model cost) (minimize (clauses->cnf clauses 8) lit-objective)
          (ok (eql best cost) (format nil "instance ~D optimum" i))
          (when model
            (ok (clauses-satisfied-p clauses (model->assignment model)))
            (ok (eql cost (objective-cost objective (model->assignment model)))
                (format nil "instance ~D model has the reported cost" i))))))))
