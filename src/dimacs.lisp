;;;; DIMACS CNF read / write.
;;;;
;;;; (read-dimacs source) -> CNF. SOURCE is an input stream, a pathname, or a
;;;;   string holding DIMACS text. Variables 1..V are allocated from the header in
;;;;   order and named by those integers (so CNF-VARIABLE-NAME of i is i).
;;;;   Accepted: comment lines starting with "c"; blank lines; one header
;;;;   "p cnf V C" before any clause; clause literals separated by whitespace,
;;;;   a clause may span lines and ends at 0; a line starting with "%" ends the
;;;;   input (SATLIB files); a last clause missing its 0 at end of input is kept.
;;;;   Errors signal SAT-DIMACS-ERROR (LINE = the line text, LINE-NUMBER 1-based)
;;;;   inside RESTART-CASE with SKIP-LINE (ignore that whole line and go on):
;;;;     a token that is not an integer; a clause before the header; a second or
;;;;     malformed header; a literal whose variable exceeds V.
;;;;   At the end, a clause count different from C signals SAT-DIMACS-ERROR
;;;;   (LINE NIL) with CONTINUE (accept the clauses read).
;;;;
;;;; (write-dimacs cnf &optional stream) -> writes "p cnf V C" then one line per
;;;;   clause, "l1 l2 ... 0", in CNF-CLAUSES order; comment lines ("c ...") may
;;;;   precede the header. STREAM NIL returns the text as a string; otherwise
;;;;   returns CNF. Auxiliary variables are written like any other index.

(in-package #:sat-protocol)

(defun %whitespace-p (char)
  (member char '(#\Space #\Tab #\Return #\Page)))

(defun %tokens (text)
  (let ((tokens '()) (start nil))
    (loop for i from 0 below (length text)
          for ch = (char text i)
          do (if (%whitespace-p ch)
                 (when start (push (subseq text start i) tokens) (setf start nil))
                 (unless start (setf start i))))
    (when start (push (subseq text start) tokens))
    (nreverse tokens)))

(defun %natural-token-p (token)
  (and (plusp (length token)) (every #'digit-char-p token)))

(defun %integer-token (token)
  "The integer TOKEN spells (optional sign, then digits), or NIL."
  (let ((digits (if (and (> (length token) 1) (find (char token 0) "+-"))
                    (subseq token 1)
                    token)))
    (and (%natural-token-p digits)
         (parse-integer token))))

(defun %read-dimacs (in)
  (let ((header nil)          ; (V C)
        (clauses '())         ; reversed
        (current '())         ; reversed literals of the open clause
        (line-number 0))
    (block lines
      (loop for raw = (read-line in nil)
            while raw
            do (incf line-number)
               (let* ((line (string-right-trim '(#\Return) raw))
                      (text (string-trim '(#\Space #\Tab) line)))
                 (flet ((bad (why)
                          (restart-case (error 'sat-dimacs-error :line line :line-number line-number
                                                                 :message why)
                            (skip-line ()
                              :report "Ignore this line and go on."
                              nil))))
                   (cond ((zerop (length text)))
                         ((char= (char text 0) #\c))
                         ((char= (char text 0) #\%) (return-from lines))
                         ((char= (char text 0) #\p)
                          (let ((tokens (%tokens text)))
                            (cond (header (bad "second header"))
                                  ((and (= 4 (length tokens))
                                        (string= "p" (first tokens))
                                        (string= "cnf" (second tokens))
                                        (every #'%natural-token-p (cddr tokens)))
                                   (setf header (mapcar #'parse-integer (cddr tokens))))
                                  (t (bad "malformed header, expected \"p cnf V C\"")))))
                         (t
                          (let ((ints (mapcar #'%integer-token (%tokens text))))
                            (cond ((member nil ints) (bad "token is not an integer"))
                                  ((null header) (bad "clause before the header"))
                                  ((find-if (lambda (l) (> (abs l) (first header))) ints)
                                   (bad "variable exceeds the header's count"))
                                  (t ;; the whole line is valid: commit it
                                   (dolist (l ints)
                                     (if (zerop l)
                                         (progn (push (nreverse current) clauses)
                                                (setf current '()))
                                         (push l current))))))))))))
    (when current
      (push (nreverse current) clauses))
    (setf clauses (nreverse clauses))
    (when (and header (/= (second header) (length clauses)))
      (restart-case (error 'sat-dimacs-error
                           :line nil
                           :message (format nil "header says ~D clause~:P, read ~D"
                                            (second header) (length clauses)))
        (continue ()
          :report "Accept the clauses read."
          nil)))
    (let ((cnf (make-cnf)))
      (when header
        (loop for i from 1 to (first header) do (cnf-ensure-variable cnf i)))
      (dolist (c clauses cnf)
        (cnf-add-clause cnf c)))))

(defun read-dimacs (source)
  (etypecase source
    (stream (%read-dimacs source))
    (pathname (with-open-file (in source :direction :input) (%read-dimacs in)))
    (string (with-input-from-string (in source) (%read-dimacs in)))))

(defun %write-dimacs (cnf out)
  (format out "p cnf ~D ~D~%" (cnf-variable-count cnf) (cnf-clause-count cnf))
  (dolist (c (cnf-clauses cnf))
    (format out "~{~D ~}0~%" c)))

(defun write-dimacs (cnf &optional stream)
  (cond ((null stream) (with-output-to-string (out) (%write-dimacs cnf out)))
        (t (%write-dimacs cnf (if (eq stream t) *standard-output* stream))
           cnf)))
