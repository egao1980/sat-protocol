;;;; DIMACS CNF read / write. Bodies are stubs.
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

(defun read-dimacs (source)
  (declare (ignore source))
  (%sat-pending 'read-dimacs))

(defun write-dimacs (cnf &optional stream)
  (declare (ignore cnf stream))
  (%sat-pending 'write-dimacs))
