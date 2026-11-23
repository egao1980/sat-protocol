;;;; Cardinality and pseudo-Boolean constraints (0.2, Track L slice L2b-1).
;;;; Formula constructors (an :AT-MOST node, formula.lisp) and CNF-level adders
;;;; (integer literals). Signatures GIVEN; bodies are %L2B1-PENDING stubs.
;;;;
;;;; ------------------------------------------------------------ constraints
;;;; Every constraint here is one linear inequality over literals,
;;;;     sum of w_i over the true L_i  <=  K
;;;; with non-negative integer weights w_i and an integer bound K. Cardinality
;;;; constraints are the unit-weight case; "at least" is "at most" over the
;;;; complemented literals: sum [L_i] >= k  <=>  sum [not L_i] <= n - k.
;;;;
;;;; ---------------------------------------------------------------- arguments
;;;; LITERALS (formula level): a list of literal formulas, bare names (the
;;;; positive literal) or the constants (sat-true) / (sat-false). Duplicates and
;;;; complementary pairs are allowed and counted as separate operands. Any other
;;;; formula, or NIL, signals SAT-INVALID-FORMULA (DATUM = the element) inside
;;;; RESTART-CASE with USE-VALUE (a replacement element, checked again).
;;;; TERMS: a list of (weight . literal) conses; a non-cons element or a weight
;;;; that is not a non-negative integer signals TYPE-ERROR.
;;;; K: an integer, else TYPE-ERROR (any integer: negative and large bounds fold).
;;;; ENCODING: one of :AUTO :PAIRWISE :SEQUENTIAL :TOTALIZER :BDD, else TYPE-ERROR.
;;;; Every encoding accepts every weight; the arguments are checked before any
;;;; folding, so a bad argument signals even when the constraint would fold.
;;;;
;;;; ------------------------------------------------------- folding (formulas)
;;;; (sat-pb-at-most terms k &key (encoding :auto)), exactly:
;;;;   1. Terms of weight 0 are dropped. A (sat-true) literal subtracts its
;;;;      weight from K and is dropped; a (sat-false) literal is dropped. Bare
;;;;      names become (sat-var name). R = the remaining terms (given order,
;;;;      duplicates kept), K' = the bound left, W = the sum of R's weights.
;;;;   2. K' < 0                       -> (sat-false)
;;;;   3. W <= K' (R empty included)   -> (sat-true)
;;;;   4. K' = 0                       -> (sat-and* (mapcar #'sat-not R-literals))
;;;;   5. K' >= W - (min weight of R)  -> (sat-or* (mapcar #'sat-not R-literals))
;;;;      ("not all of them", the only violating assignment)
;;;;   6. otherwise an :AT-MOST node: operands R-literals, weights R-weights,
;;;;      bound K', encoding = ENCODING with :AUTO resolved below (n = |R|).
;;;; (sat-at-most-k literals k &key encoding) = SAT-PB-AT-MOST over (1 . l).
;;;; (sat-at-most-one literals &key encoding) = (sat-at-most-k literals 1 ...).
;;;; (sat-at-least-k literals k &key encoding)
;;;;     = (sat-at-most-k (mapcar #'sat-not literals) (- (length literals) k) ...)
;;;;     so k <= 0 -> true, k > n -> false, k = 1 -> (sat-or* literals).
;;;; (sat-exactly-one literals &key encoding)
;;;;     = (sat-and (sat-at-most-one literals ...) (sat-or* literals)).
;;;;
;;;; :AUTO, on the folded node (n operands, bound K'):
;;;;   unit weights, K' = 1:  :PAIRWISE when n <= 6, else :SEQUENTIAL
;;;;   unit weights, K' >= 2: :TOTALIZER
;;;;   other weights:         :BDD
;;;;
;;;; ---------------------------------------------------------------- encodings
;;;; Each encoding adds clauses (and fresh auxiliary variables, CNF name NIL)
;;;; such that the models of the CNF projected on its earlier variables are
;;;; exactly the earlier models that satisfy the constraint: no model is lost and
;;;; none is added. n operands, bound K (1 <= K < W after folding).
;;;;   :PAIRWISE    no auxiliary. One clause (-L_i1 ... -L_im) per minimal set of
;;;;                operand positions whose weights sum to more than K. Unit
;;;;                weights: every (K+1)-subset; K = 1: the n(n-1)/2 binary
;;;;                clauses. C(n, K+1) clauses: for small n.
;;;;   :SEQUENTIAL  Sinz's sequential counter; for weights, the sequential weight
;;;;                counter (Hoelldobler, Manthey, Steinke 2012). Auxiliaries
;;;;                s(i,j) = "operands 1..i weigh at least j", j <= K.
;;;;   :TOTALIZER   Bailleux-Boufkhad totalizer, outputs capped at K+1; for
;;;;                weights, the generalized totalizer (GTE: one output per
;;;;                reachable sum <= K+1 at each node).
;;;;   :BDD         The BDD of the 0.1 MINIMIZE bound: node N(i,k) = "operands
;;;;                i.. weigh at most k", clauses (-N -L_i N(i+1,k-w_i)) and
;;;;                (-N L_i N(i+1,k)), constant children folded, nodes shared.
;;;; Every encoding but :PAIRWISE adds at most n * (K + 1) auxiliaries.
;;;; Untested guidance: prefer encodings on which unit propagation is complete
;;;; (assigning K' true operands forces the others false), as the cited ones are.
;;;;
;;;; ------------------------------------------------------------ CNF level
;;;; The same constraints over integer literals of an existing CNF, added in
;;;; place; each returns the CNF.
;;;; (cnf-add-pb-at-most cnf terms k &key (encoding :auto))
;;;;     TERMS: ((weight . integer-literal) ...).
;;;; (cnf-add-at-most-k cnf literals k &key encoding)
;;;; (cnf-add-at-most-one cnf literals &key encoding)
;;;; (cnf-add-at-least-k cnf literals k &key encoding)   at most n-k of the -L
;;;; (cnf-add-exactly-one cnf literals &key encoding)    at most one, plus the
;;;;                                                     clause (L...)
;;;; LITERALS are integer literals as for CNF-ADD-CLAUSE: a literal that is 0,
;;;; not an integer, or beyond CNF-VARIABLE-COUNT signals SAT-INVALID-FORMULA
;;;; (DATUM = that literal), and nothing is added (every literal is checked
;;;; first). Weights, K and ENCODING are checked as above (TYPE-ERROR).
;;;; Folding mirrors the formula rules (there are no constants): weight-0 terms
;;;; are dropped; K < 0 adds the empty clause; W <= K adds nothing; K = 0 adds
;;;; the unit clause (-L) per term; K >= W - min weight adds the one clause
;;;; (-L ...); otherwise the encoding (:AUTO resolved as above). TO-CNF of a
;;;; top-level :AT-MOST conjunct adds exactly what CNF-ADD-PB-AT-MOST adds for
;;;; its operands' integer literals, weights, bound and encoding.

(in-package #:sat-protocol)

(deftype %encoding ()
  "GIVEN: the ENCODING argument of the constructors and adders (0.2)."
  '(member :auto :pairwise :sequential :totalizer :bdd))

;;; ------------------------------------------------------------ formula level

(defun sat-pb-at-most (terms k &key (encoding :auto))
  "Sum of the weights of the true literals of TERMS ((weight . literal) ...) is
at most K. Folds by the rules in this file's header; otherwise an :AT-MOST
formula encoded with ENCODING (:AUTO :PAIRWISE :SEQUENTIAL :TOTALIZER :BDD)."
  (declare (ignore terms k encoding))
  (%l2b1-pending 'sat-pb-at-most))

(defun sat-at-most-k (literals k &key (encoding :auto))
  "At most K of LITERALS are true: SAT-PB-AT-MOST with unit weights."
  (declare (ignore literals k encoding))
  (%l2b1-pending 'sat-at-most-k))

(defun sat-at-most-one (literals &key (encoding :auto))
  "At most one of LITERALS is true: (sat-at-most-k literals 1 :encoding encoding)."
  (declare (ignore literals encoding))
  (%l2b1-pending 'sat-at-most-one))

(defun sat-at-least-k (literals k &key (encoding :auto))
  "At least K of LITERALS are true: at most (length LITERALS) - K of their
complements."
  (declare (ignore literals k encoding))
  (%l2b1-pending 'sat-at-least-k))

(defun sat-exactly-one (literals &key (encoding :auto))
  "Exactly one of LITERALS is true:
(sat-and (sat-at-most-one literals :encoding encoding) (sat-or* literals))."
  (declare (ignore literals encoding))
  (%l2b1-pending 'sat-exactly-one))

;;; ---------------------------------------------------------------- CNF level

(defun cnf-add-pb-at-most (cnf terms k &key (encoding :auto))
  "Add sum of w over the true integer literals of TERMS <= K to CNF. Returns CNF."
  (declare (ignore cnf terms k encoding))
  (%l2b1-pending 'cnf-add-pb-at-most))

(defun cnf-add-at-most-k (cnf literals k &key (encoding :auto))
  "Add: at most K of the integer LITERALS are true. Returns CNF."
  (declare (ignore cnf literals k encoding))
  (%l2b1-pending 'cnf-add-at-most-k))

(defun cnf-add-at-most-one (cnf literals &key (encoding :auto))
  "Add: at most one of the integer LITERALS is true. Returns CNF."
  (declare (ignore cnf literals encoding))
  (%l2b1-pending 'cnf-add-at-most-one))

(defun cnf-add-at-least-k (cnf literals k &key (encoding :auto))
  "Add: at least K of the integer LITERALS are true. Returns CNF."
  (declare (ignore cnf literals k encoding))
  (%l2b1-pending 'cnf-add-at-least-k))

(defun cnf-add-exactly-one (cnf literals &key (encoding :auto))
  "Add: exactly one of the integer LITERALS is true. Returns CNF."
  (declare (ignore cnf literals encoding))
  (%l2b1-pending 'cnf-add-exactly-one))

;;; --------------------------------------------------- TO-CNF hooks (cnf.lisp)

(defun %encode-at-most (cnf node guard)
  "TO-CNF of a top-level :AT-MOST conjunct NODE: its encoding, as
CNF-ADD-PB-AT-MOST over the operands' integer literals. GUARD: NIL, or the
integer literal of an UNSAT-CORE selector; then the clauses make GUARD imply the
constraint (and impose nothing when GUARD is false)."
  (declare (ignore cnf node guard))
  (%l2b1-pending '%encode-at-most))

(defun %pg-at-most (cnf node pos neg)
  "%PG for a nested :AT-MOST NODE: a fresh auxiliary X; POS: X -> constraint;
NEG: constraint -> X (the complement, at most W - K - 1 of the negated
operands, implies X). Returns X."
  (declare (ignore cnf node pos neg))
  (%l2b1-pending '%pg-at-most))
