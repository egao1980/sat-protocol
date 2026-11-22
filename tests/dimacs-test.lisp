(in-package #:sat-protocol/tests)

;;; DIMACS read / write.

(defun lines (&rest lines)
  (format nil "~{~A~%~}" lines))

(deftest read-tiny
  (let ((cnf (read-dimacs (fixture-path "tiny-sat.cnf"))))
    (ok (= 3 (cnf-variable-count cnf)))
    (ok (equal '((1 -3) (2 3 -1)) (cnf-clauses cnf)))
    (ok (equal '(1 2 3) (cnf-user-variables cnf)) "variables are named by their integers")))

(deftest read-satlib-layout
  (let ((cnf (read-dimacs (fixture-path "satlib-style.cnf"))))
    (ok (= 4 (cnf-variable-count cnf)))
    (ok (equal '((1 -2 3) (-1 4) (2 -3)) (cnf-clauses cnf)) "spanning lines, two per line, % ends")))

(deftest read-sources
  (let ((text (lines "p cnf 2 1" "1 -2 0")))
    (ok (equal '((1 -2)) (cnf-clauses (read-dimacs text))) "a string is DIMACS text")
    (ok (equal '((1 -2)) (with-input-from-string (s text) (cnf-clauses (read-dimacs s)))) "a stream")))

(deftest read-unused-variables
  (let ((cnf (read-dimacs (lines "p cnf 5 1" "2 0"))))
    (ok (= 5 (cnf-variable-count cnf)) "all header variables allocated")
    (ok (equal '(1 2 3 4 5) (cnf-user-variables cnf)))))

(deftest read-missing-final-zero
  (ok (equal '((1) (-1 2)) (cnf-clauses (read-dimacs (lines "p cnf 2 2" "1 0" "-1 2"))))))

(deftest read-empty-clause
  (ok (equal '(()) (cnf-clauses (read-dimacs (lines "p cnf 1 1" "0"))))))

(deftest-parametrize read-errors
    ((text line-number)
     :ids ("bad-token" "before-header" "second-header" "bad-header" "out-of-range")
     ((lines "p cnf 2 1" "1 x 0") 2)
     ((lines "1 2 0" "p cnf 2 1") 1)
     ((lines "p cnf 2 1" "p cnf 2 1" "1 0") 2)
     ((lines "p dnf 2 1" "1 0") 1)
     ((lines "c comment" "p cnf 2 1" "1 3 0") 3))
  (ok (signals (read-dimacs text) 'sat-dimacs-error))
  (ok (eql line-number (handler-case (read-dimacs text)
                         (sat-dimacs-error (c) (sat-dimacs-error-line-number c))))))

(deftest read-error-line-text
  (ok (equal "1 x 0" (handler-case (read-dimacs (lines "p cnf 2 2" "1 x 0" "2 0"))
                       (sat-dimacs-error (c) (sat-dimacs-error-line c))))))

(deftest read-skip-line
  (ok (equal '((2))
             (handler-bind ((sat-dimacs-error (lambda (c)
                                                (if (sat-dimacs-error-line c)
                                                    (skip-line c)
                                                    (continue c)))))
               (cnf-clauses (read-dimacs (lines "p cnf 2 2" "1 x 0" "2 0")))))
      "SKIP-LINE drops the bad line; CONTINUE accepts the short count"))

(deftest read-count-mismatch
  (let ((text (lines "p cnf 2 3" "1 0" "2 0")))
    (ok (signals (read-dimacs text) 'sat-dimacs-error))
    (ok (null (handler-case (read-dimacs text)
                (sat-dimacs-error (c) (sat-dimacs-error-line c))))
        "end-of-input error has no line")
    (ok (equal '((1) (2))
               (handler-bind ((sat-dimacs-error #'continue))
                 (cnf-clauses (read-dimacs text)))))))

(deftest write-format
  (let* ((cnf (clauses->cnf '((1 -2) (2)) 2))
         (text (write-dimacs cnf nil))
         (body (remove-if (lambda (l) (or (zerop (length l)) (char= #\c (char l 0))))
                          (uiop:split-string text :separator '(#\Newline)))))
    (ok (stringp text))
    (ok (equal '("p cnf 2 2" "1 -2 0" "2 0") body))))

(deftest write-to-stream
  (let* ((cnf (clauses->cnf '((1)) 1))
         (result nil)
         (text (with-output-to-string (s) (setf result (write-dimacs cnf s)))))
    (ok (eq cnf result) "returns the CNF")
    (ok (search "p cnf 1 1" text))))

(deftest write-read-round-trip
  (let ((rng (make-rng 31)))
    (dotimes (i 10)
      (let* ((cnf (to-cnf (f (random-sexp rng '("a" "b" "c" "d" "e") 4))))
             (back (read-dimacs (write-dimacs cnf nil))))
        (ok (equal (cnf-clauses cnf) (cnf-clauses back)) (format nil "round trip ~D" i))
        (ok (= (cnf-variable-count cnf) (cnf-variable-count back)))))))

(deftest read-fixture-counts
  (let ((cnf (read-dimacs (fixture-path "php-4-3.cnf"))))
    (ok (= 12 (cnf-variable-count cnf)))
    (ok (= 22 (cnf-clause-count cnf))))
  (let ((cnf (read-dimacs (fixture-path "rand3-20-91-sat.cnf"))))
    (ok (= 20 (cnf-variable-count cnf)))
    (ok (= 91 (cnf-clause-count cnf)))
    (ok (every (lambda (c) (= 3 (length c))) (cnf-clauses cnf)))))
