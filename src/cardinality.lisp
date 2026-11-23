;;;; Cardinality and pseudo-Boolean constraints (0.2, Track L slice L2b-1).
;;;; Formula constructors (an :AT-MOST node, formula.lisp) and CNF-level adders
;;;; (integer literals). Signatures GIVEN; implemented here. One encoding engine
;;;; (%ADD-PB) serves the adders, TO-CNF and MINIMIZE (minimize.lisp reuses
;;;; %BDD-BUILDER and %GTE for its bounds).
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


;;; ---------------------------------------------------------------- arguments

(defun %card-literal (element)
  "ELEMENT of a formula-level LITERALS list as a formula: a literal formula or a
constant as is, a bare non-NIL name as (sat-var name). Anything else signals
SAT-INVALID-FORMULA inside RESTART-CASE with USE-VALUE (checked again)."
  (loop
    (cond ((formula-p element)
           (when (or (literal-p element)
                     (member (formula-operator element) '(:true :false)))
             (return element)))
          (element (return (sat-var element))))
    (restart-case (error 'sat-invalid-formula
                         :datum element
                         :message "a constraint operand must be a literal or a constant")
      (use-value (value)
        :report "Use another operand (checked again)."
        :interactive %read-value
        (setf element value)))))

(defun %check-cnf-literal (cnf literal)
  "LITERAL as CNF-ADD-CLAUSE checks it: SAT-INVALID-FORMULA (DATUM = LITERAL)
unless it is a non-zero integer within CNF-VARIABLE-COUNT."
  (unless (and (integerp literal) (/= literal 0) (<= (abs literal) (cnf-variable-count cnf)))
    (error 'sat-invalid-formula :datum literal :message "not a literal of this CNF"))
  literal)

(defun %check-term (term)
  "TERM as (weight . x) with a non-negative integer weight, else TYPE-ERROR
(CHECK-TYPE, so STORE-VALUE may replace it). Returns the checked term."
  (check-type term cons)
  (let ((weight (car term)))
    (check-type weight (integer 0 *))
    (cons weight (cdr term))))

(defun %resolve-encoding (encoding terms k)
  ":AUTO on a folded constraint (TERMS ((w . l) ...), bound K); any other
ENCODING as is."
  (if (eq encoding :auto)
      (cond ((notevery (lambda (term) (eql 1 (car term))) terms) :bdd)
            ((= k 1) (if (<= (length terms) 6) :pairwise :sequential))
            (t :totalizer))
      encoding))

;;; ------------------------------------------------------------ formula level

(defun %pb-formula (terms k encoding)
  "Fold TERMS ((weight . literal-or-constant-formula) ...), all checked, by the
rules in this file's header."
  (let ((rest '()))
    (loop for term in terms
          for (weight . literal) = term
          do (case (formula-operator literal)
               (:true (decf k weight))
               (:false)
               (t (unless (zerop weight) (push term rest)))))
    (setf rest (nreverse rest))
    (let ((total (reduce #'+ rest :key #'car))
          (negated (lambda () (mapcar (lambda (term) (sat-not (cdr term))) rest))))
      (cond ((minusp k) (sat-false))
            ((<= total k) (sat-true))
            ((zerop k) (sat-and* (funcall negated)))
            ((>= k (- total (reduce #'min rest :key #'car))) (sat-or* (funcall negated)))
            (t (%make-at-most (mapcar #'cdr rest) (mapcar #'car rest) k
                              (%resolve-encoding encoding rest k)))))))

(defun sat-pb-at-most (terms k &key (encoding :auto))
  "Sum of the weights of the true literals of TERMS ((weight . literal) ...) is
at most K. Folds by the rules in this file's header; otherwise an :AT-MOST
formula encoded with ENCODING (:AUTO :PAIRWISE :SEQUENTIAL :TOTALIZER :BDD)."
  (check-type k integer)
  (check-type encoding %encoding)
  (check-type terms list)
  (%pb-formula (mapcar (lambda (term)
                         (let ((term (%check-term term)))
                           (cons (car term) (%card-literal (cdr term)))))
                       terms)
               k encoding))

(defun sat-at-most-k (literals k &key (encoding :auto))
  "At most K of LITERALS are true: SAT-PB-AT-MOST with unit weights."
  (check-type k integer)
  (check-type encoding %encoding)
  (check-type literals list)
  (%pb-formula (mapcar (lambda (l) (cons 1 (%card-literal l))) literals) k encoding))

(defun sat-at-most-one (literals &key (encoding :auto))
  "At most one of LITERALS is true: (sat-at-most-k literals 1 :encoding encoding)."
  (sat-at-most-k literals 1 :encoding encoding))

(defun sat-at-least-k (literals k &key (encoding :auto))
  "At least K of LITERALS are true: at most (length LITERALS) - K of their
complements."
  (check-type k integer)
  (check-type encoding %encoding)
  (check-type literals list)
  (let ((checked (mapcar #'%card-literal literals)))
    (%pb-formula (mapcar (lambda (l) (cons 1 (sat-not l))) checked)
                 (- (length checked) k) encoding)))

(defun sat-exactly-one (literals &key (encoding :auto))
  "Exactly one of LITERALS is true:
(sat-and (sat-at-most-one literals :encoding encoding) (sat-or* literals))."
  (check-type encoding %encoding)
  (check-type literals list)
  ;; Checked once, so a USE-VALUE replacement is used by both halves.
  (let ((checked (mapcar #'%card-literal literals)))
    (sat-and (%pb-formula (mapcar (lambda (l) (cons 1 l)) checked) 1 encoding)
             (sat-or* checked))))

;;; ---------------------------------------------------------------- encodings
;;; Every encoding below takes folded integer TERMS ((w . literal) ...), all
;;; weights >= 1, a bound K with 1 <= K < W - (min weight), and EMIT, a function
;;; that adds one clause (guarded by %ADD-PB when needed). Auxiliaries are
;;; allocated in CNF with name NIL, in a fixed order, so TO-CNF and the adders
;;; produce the same CNF.

(defun %pairwise (terms k emit)
  "One clause (-L ...) per minimal set of positions whose weights exceed K:
depth-first over increasing positions, a set is closed as soon as it exceeds K,
and it is minimal when dropping its lightest element brings it back to <= K."
  (let* ((v (coerce terms 'vector))
         (n (length v)))
    (labels ((walk (start sum least chosen)
               (loop for i from start below n
                     do (destructuring-bind (weight . literal) (aref v i)
                          (let ((sum (+ sum weight))
                                (least (if least (min least weight) weight))
                                (chosen (cons (- literal) chosen)))
                            (if (> sum k)
                                (when (<= (- sum least) k)
                                  (funcall emit (reverse chosen)))
                                (walk (1+ i) sum least chosen)))))))
      (walk 0 0 nil '()))))

(defun %sequential (cnf terms k emit)
  "Sinz's sequential counter; for weights, the sequential weight counter.
s(i,j) = \"operands 1..i weigh at least j\" for i < n, j = 1..K: (n-1)K
auxiliaries, allocated row by row."
  (let* ((v (coerce terms 'vector))
         (n (length v))
         (previous nil))                ; row i-1: s(i-1, j) at index j-1
    (dotimes (i n)
      (destructuring-bind (weight . x) (aref v i)
        (let ((row (when (< i (1- n))
                     (let ((r (make-array k)))
                       (dotimes (j k r) (setf (aref r j) (cnf-ensure-variable cnf nil)))))))
          (when row
            (loop for j from 1 to (min weight k)
                  do (funcall emit (list (- x) (aref row (1- j)))))
            (when previous
              (loop for j from 1 to k
                    do (funcall emit (list (- (aref previous (1- j))) (aref row (1- j)))))
              (loop for j from 1 to (- k weight)
                    do (funcall emit (list (- x) (- (aref previous (1- j)))
                                           (aref row (1- (+ j weight))))))))
          ;; Overflow: x_i true on top of a prefix of at least K + 1 - w_i.
          (cond ((> weight k) (funcall emit (list (- x))))
                (previous (funcall emit (list (- x) (- (aref previous (- k weight)))))))
          (setf previous row))))))

(defun %gte (cnf terms cap emit)
  "Generalized totalizer over TERMS ((w . literal) ...), w >= 1, sums capped at
CAP. Leaves are the literals themselves; an internal node gets one auxiliary
per reachable capped sum of its leaves, with the clauses \"subtree sum >= v ->
o_v\" only. Returns the root's outputs ((v . literal) ...), ascending. With
unit weights this is the Bailleux-Boufkhad totalizer and the outputs are
contiguous; with weights an output o_v is forced by the sums that reach v
exactly, so forbidding \"sum >= c\" takes every root output with v >= c."
  (labels ((node (terms n)
             (if (= n 1)
                 (destructuring-bind (weight . literal) (first terms)
                   (list (cons (min weight cap) literal)))
                 (let* ((half (floor n 2))
                        (a (node terms half))
                        (b (node (nthcdr half terms) (- n half)))
                        (sums (sort (remove-duplicates
                                     (append (mapcar #'car a) (mapcar #'car b)
                                             (loop for x in (mapcar #'car a)
                                                   nconc (loop for y in (mapcar #'car b)
                                                               collect (min (+ x y) cap)))))
                                    #'<))
                        (outputs (mapcar (lambda (sum) (cons sum (cnf-ensure-variable cnf nil)))
                                         sums)))
                   (flet ((out (sum) (cdr (assoc sum outputs))))
                     (loop for (x . lx) in a do (funcall emit (list (- lx) (out x))))
                     (loop for (y . ly) in b do (funcall emit (list (- ly) (out y))))
                     (loop for (x . lx) in a
                           do (loop for (y . ly) in b
                                    do (funcall emit (list (- lx) (- ly) (out (min (+ x y) cap)))))))
                   outputs))))
    (node terms (length terms))))

(defun %bdd-builder (cnf terms emit &key propagating)
  "The BDD of the 0.1 MINIMIZE bound over TERMS ((w . literal) ...): returns a
function of K giving the literal of node N(0,K) (\"the terms weigh at most
K\"), or :TRUE / :FALSE for a constant node. N(i,k) gets the clauses
(-N -L_i N(i+1,k-w_i)) and (-N L_i N(i+1,k)), constant children folded. Nodes
are memoised across calls of the function and allocated in post-order.
PROPAGATING (MINIMIZE's bounds, minimize.lisp): the second clause is the
stronger (-N N(i+1,k)), also sound (dropping operand i never raises the sum).
Then unit propagation forces false every operand that no longer fits, whatever
the decision order; with the clause above it does so only for operands
reached in BDD order, which an :ORDER hook can defeat."
  (let* ((v (coerce terms 'vector))
         (n (length v))
         (suffix (make-array (1+ n) :initial-element 0))
         (memo (make-hash-table :test 'equal)))
    (loop for i from (1- n) downto 0
          do (setf (aref suffix i) (+ (aref suffix (1+ i)) (car (aref v i)))))
    (labels ((node (i k)
               (cond ((minusp k) :false)
                     ((>= k (aref suffix i)) :true)
                     (t (let ((key (cons i k)))
                          (or (gethash key memo)
                              (setf (gethash key memo)
                                    (destructuring-bind (weight . literal) (aref v i)
                                      (let* ((hi (node (1+ i) (- k weight)))
                                             (lo (node (1+ i) k))
                                             (x (cnf-ensure-variable cnf nil)))
                                        (flet ((imply (lit child)
                                                 (unless (eq child :true)
                                                   (funcall emit (if (eq child :false)
                                                                     (list (- x) lit)
                                                                     (list (- x) lit child))))))
                                          (imply (- literal) hi)
                                          (if propagating
                                              (unless (eq lo :true) (funcall emit (list (- x) lo)))
                                              (imply literal lo)))
                                        x)))))))))
      (lambda (k) (node 0 k)))))

(defun %add-pb (cnf terms k encoding guard)
  "The engine: sum of w over the true integer literals of TERMS <= K, added to
CNF. TERMS, K and ENCODING are already checked. Folds by the CNF-level rules,
resolves :AUTO, then encodes. GUARD: NIL, or an integer literal; then every
clause carries -GUARD (GUARD implies the constraint, and nothing is imposed
when GUARD is false). Returns CNF."
  (flet ((emit (clause)
           (cnf-add-clause cnf (if guard (cons (- guard) clause) clause))))
    (let* ((rest (remove 0 terms :key #'car))
           (total (reduce #'+ rest :key #'car)))
      (cond ((minusp k) (emit '()))
            ((<= total k))
            ((zerop k) (dolist (term rest) (emit (list (- (cdr term))))))
            ((>= k (- total (reduce #'min rest :key #'car)))
             (emit (mapcar (lambda (term) (- (cdr term))) rest)))
            (t (ecase (%resolve-encoding encoding rest k)
                 (:pairwise (%pairwise rest k #'emit))
                 (:sequential (%sequential cnf rest k #'emit))
                 (:totalizer
                  (let ((outputs (%gte cnf rest (1+ k) #'emit)))
                    (emit (list (- (cdr (assoc (1+ k) outputs)))))))
                 (:bdd
                  (let ((root (funcall (%bdd-builder cnf rest #'emit) k)))
                    (case root
                      (:true)
                      (:false (emit '()))
                      (t (emit (list root))))))))))
    cnf))

;;; ---------------------------------------------------------------- CNF level

(defun cnf-add-pb-at-most (cnf terms k &key (encoding :auto))
  "Add sum of w over the true integer literals of TERMS <= K to CNF. Returns CNF."
  (check-type k integer)
  (check-type encoding %encoding)
  (check-type terms list)
  (let ((checked (mapcar #'%check-term terms)))
    (dolist (term checked) (%check-cnf-literal cnf (cdr term)))
    (%add-pb cnf checked k encoding nil)))

(defun %check-cnf-literals (cnf literals)
  (check-type literals list)
  (dolist (l literals literals) (%check-cnf-literal cnf l)))

(defun cnf-add-at-most-k (cnf literals k &key (encoding :auto))
  "Add: at most K of the integer LITERALS are true. Returns CNF."
  (check-type k integer)
  (check-type encoding %encoding)
  (%check-cnf-literals cnf literals)
  (%add-pb cnf (mapcar (lambda (l) (cons 1 l)) literals) k encoding nil))

(defun cnf-add-at-most-one (cnf literals &key (encoding :auto))
  "Add: at most one of the integer LITERALS is true. Returns CNF."
  (cnf-add-at-most-k cnf literals 1 :encoding encoding))

(defun cnf-add-at-least-k (cnf literals k &key (encoding :auto))
  "Add: at least K of the integer LITERALS are true. Returns CNF."
  (check-type k integer)
  (check-type encoding %encoding)
  (%check-cnf-literals cnf literals)
  (%add-pb cnf (mapcar (lambda (l) (cons 1 (- l))) literals) (- (length literals) k)
           encoding nil))

(defun cnf-add-exactly-one (cnf literals &key (encoding :auto))
  "Add: exactly one of the integer LITERALS is true. Returns CNF."
  (check-type encoding %encoding)
  (%check-cnf-literals cnf literals)
  (%add-pb cnf (mapcar (lambda (l) (cons 1 l)) literals) 1 encoding nil)
  (cnf-add-clause cnf literals))

;;; --------------------------------------------------- TO-CNF hooks (cnf.lisp)

(defun %node-terms (cnf node)
  "The ((weight . integer-literal) ...) of an :AT-MOST NODE whose variables CNF
already has."
  (mapcar (lambda (weight operand) (cons weight (cnf-literal cnf operand)))
          (formula-weights node) (formula-operands node)))

(defun %encode-at-most (cnf node guard)
  "TO-CNF of a top-level :AT-MOST conjunct NODE: its encoding, as
CNF-ADD-PB-AT-MOST over the operands' integer literals. GUARD: NIL, or the
integer literal of an UNSAT-CORE selector; then the clauses make GUARD imply the
constraint (and impose nothing when GUARD is false)."
  (%add-pb cnf (%node-terms cnf node) (formula-bound node) (formula-encoding node) guard))

(defun %pg-at-most (cnf node pos neg)
  "%PG for a nested :AT-MOST NODE: a fresh auxiliary X; POS: X -> constraint;
NEG: constraint -> X (the complement, at most W - K - 1 of the negated
operands, implies X). Returns X."
  (let ((terms (%node-terms cnf node))
        (x (cnf-ensure-variable cnf nil))
        (bound (formula-bound node))
        (encoding (formula-encoding node)))
    (when pos
      (%add-pb cnf terms bound encoding x))
    (when neg
      ;; not (sum w [L] <= K)  <=>  sum w [not L] <= W - K - 1, under -X.
      (%add-pb cnf (mapcar (lambda (term) (cons (car term) (- (cdr term)))) terms)
               (- (reduce #'+ terms :key #'car) bound 1) encoding (- x)))
    x))
