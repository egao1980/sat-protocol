;;;; Oracles for the 0.2 optimisation tests (L2b-1). GIVEN test code, no stubs.
;;;;
;;;; - Brute-force optima over integer clauses (BRUTE-MODELS) and over formula
;;;;   sexps (ALL-ASSIGNMENTS), plain and lexicographic.
;;;; - The weighted chain family: positions 0..P-1, each with a one-hot choice
;;;;   among its labels (variables (:x p l)); hard no-goods between adjacent
;;;;   positions; soft costs per label (unary) and per adjacent label pair, one
;;;;   cost vector per objective level. A pair with a cost gets a cost literal
;;;;   (:y p l m) with the clause x(p,l) & x(p+1,m) -> y(p,l,m); its objective
;;;;   entry is (cost . y). CHAIN-DP is the dynamic-programming (Viterbi) oracle
;;;;   over cost vectors, compared lexicographically.

(in-package #:sat-protocol/conformance)

(defparameter *strategies* '(:linear-bdd :linear-totalizer :stratified :core-guided)
  "Every MINIMIZE :STRATEGY of sat-protocol 0.2.")

;;; ------------------------------------------------------------ literals, costs

(defun lit-formula (lit)
  "The literal formula of the integer literal LIT (variables named 1..N)."
  (if (plusp lit) (sat-var lit) (sat-not (sat-var (- lit)))))

(defun int-objective->literals (objective)
  "((w . integer-literal) ...) -> ((w . literal-formula) ...)."
  (mapcar (lambda (entry) (cons (car entry) (lit-formula (cdr entry)))) objective))

(defun int-cost (objective value-fn)
  "Cost of OBJECTIVE ((w . integer-literal) ...); VALUE-FN: index -> boolean."
  (loop for (weight . lit) in objective
        when (if (plusp lit) (funcall value-fn lit) (not (funcall value-fn (- lit))))
          sum weight))

(defun random-int-objective (rng nvars nterms weights)
  "NTERMS entries (w . l), w drawn from WEIGHTS, l a random literal over 1..NVARS
(repeats and complementary pairs allowed)."
  (loop repeat nterms
        collect (cons (nth (rng-int rng (length weights)) weights)
                      (let ((v (1+ (rng-int rng nvars))))
                        (if (zerop (rng-int rng 2)) v (- v))))))

(defun bits-fn (bits)
  (lambda (i) (= 1 (sbit bits i))))

(defun brute-optimum (clauses nvars objective)
  "Least cost of OBJECTIVE over the models of CLAUSES, or NIL when UNSAT."
  (let ((costs (mapcar (lambda (bits) (int-cost objective (bits-fn bits)))
                       (brute-models clauses nvars))))
    (and costs (reduce #'min costs))))

(defun lex< (a b)
  "Lexicographic < on equal-length lists of integers."
  (loop for x in a for y in b
        do (cond ((< x y) (return t))
                 ((> x y) (return nil)))
        finally (return nil)))

(defun lex-min (vectors)
  (reduce (lambda (a b) (if (lex< b a) b a)) vectors))

(defun brute-lex-optimum (clauses nvars levels)
  "Lexicographically least cost vector over LEVELS (integer objectives), or NIL."
  (let ((vectors (mapcar (lambda (bits)
                           (mapcar (lambda (o) (int-cost o (bits-fn bits))) levels))
                         (brute-models clauses nvars))))
    (and vectors (lex-min vectors))))

(defun name-cost (objective model)
  "Cost of a name-level OBJECTIVE ((w . literal-formula-or-name) ...) under MODEL."
  (loop for (weight . lit) in objective
        when (eq (and (cdr (assoc (literal-name lit) model :test #'equal)) t)
                 (literal-positive-p lit))
          sum weight))

(defun random-name-objective (rng names nterms weights)
  (loop repeat nterms
        collect (cons (nth (rng-int rng (length weights)) weights)
                      (let ((v (sat-var (nth (rng-int rng (length names)) names))))
                        (if (zerop (rng-int rng 2)) v (sat-not v))))))

(defun sexp-optimum (sexp names objective)
  "Least cost of OBJECTIVE over the assignments of NAMES satisfying SEXP, or NIL."
  (let ((costs (loop for env in (all-assignments names)
                     when (sexp-eval sexp env)
                       collect (name-cost objective env))))
    (and costs (reduce #'min costs))))

;;; ---------------------------------------------------------------- chains

(defstruct (chain (:constructor %make-chain))
  labels      ; list: number of labels at each position
  levels      ; number of objective levels
  nogoods     ; list of (p l m): x(p,l) and x(p+1,m) never both
  unary       ; list of ((p l) . cost-list)
  pair)       ; list of ((p l m) . cost-list), pairs that are not no-goods

(defun random-chain (rng &key (positions 3) (min-labels 2) (max-labels 3) (levels 1)
                           (nogood-percent 20) (cost-percent 60) (max-cost 3))
  "A random chain. Each unary and pair entry gets, per level, a cost in
1..MAX-COST with probability COST-PERCENT, else 0; entries all 0 are left out."
  (let ((labels (loop repeat positions
                      collect (+ min-labels (rng-int rng (1+ (- max-labels min-labels))))))
        (nogoods '()) (unary '()) (pair '()))
    (flet ((costs ()
             (loop repeat levels
                   collect (if (< (rng-int rng 100) cost-percent) (1+ (rng-int rng max-cost)) 0))))
      (loop for p from 0 for n in labels
            do (dotimes (l n)
                 (let ((c (costs)))
                   (when (some #'plusp c) (push (cons (list p l) c) unary)))))
      (loop for p from 0 below (1- positions)
            do (dotimes (l (nth p labels))
                 (dotimes (m (nth (1+ p) labels))
                   (if (< (rng-int rng 100) nogood-percent)
                       (push (list p l m) nogoods)
                       (let ((c (costs)))
                         (when (some #'plusp c) (push (cons (list p l m) c) pair))))))))
    (%make-chain :labels labels :levels levels :nogoods (nreverse nogoods)
                 :unary (nreverse unary) :pair (nreverse pair))))

(defun chain-x (p l) (list :x p l))
(defun chain-y (p l m) (list :y p l m))

(defun chain-formula (chain &key encoding)
  "Hard part of CHAIN. ENCODING NIL: clause-shaped (per position one at-least-one
clause and the pairwise at-most-one clauses), so TO-CNF adds no auxiliary.
Otherwise SAT-EXACTLY-ONE with that :ENCODING per position."
  (let ((terms '()))
    (loop for p from 0 for n in (chain-labels chain)
          for xs = (loop for l below n collect (sat-var (chain-x p l)))
          do (if encoding
                 (push (sat-exactly-one xs :encoding encoding) terms)
                 (progn
                   (push (sat-or* xs) terms)
                   (loop for (a . more) on xs
                         do (dolist (b more)
                              (push (sat-or (sat-not a) (sat-not b)) terms))))))
    (loop for (p l m) in (chain-nogoods chain)
          do (push (sat-or (sat-not (sat-var (chain-x p l)))
                           (sat-not (sat-var (chain-x (1+ p) m))))
                   terms))
    (loop for ((p l m)) in (chain-pair chain)
          do (push (sat-or (sat-not (sat-var (chain-x p l)))
                           (sat-not (sat-var (chain-x (1+ p) m)))
                           (sat-var (chain-y p l m)))
                   terms))
    (sat-and* (nreverse terms))))

(defun chain-objective (chain &optional (level 0))
  "The plain objective of LEVEL: unary entries on x, pair entries on y."
  (append (loop for ((p l) . costs) in (chain-unary chain)
                for c = (nth level costs)
                when (plusp c) collect (cons c (sat-var (chain-x p l))))
          (loop for ((p l m) . costs) in (chain-pair chain)
                for c = (nth level costs)
                when (plusp c) collect (cons c (sat-var (chain-y p l m))))))

(defun chain-lex-objective (chain)
  (cons :lex (loop for i below (chain-levels chain) collect (chain-objective chain i))))

(defun %zero (chain) (make-list (chain-levels chain) :initial-element 0))

(defun %v+ (a b) (mapcar #'+ a b))

(defun chain-unary-costs (chain p l)
  (or (cdr (assoc (list p l) (chain-unary chain) :test #'equal)) (%zero chain)))

(defun chain-pair-costs (chain p l m)
  (or (cdr (assoc (list p l m) (chain-pair chain) :test #'equal)) (%zero chain)))

(defun chain-nogood-p (chain p l m)
  (member (list p l m) (chain-nogoods chain) :test #'equal))

(defun chain-dp (chain)
  "The lexicographically least cost vector of a feasible labelling, or NIL.
Viterbi: best(p, m) = min over l of best(p-1, l) + pair(p-1, l, m) + unary(p, m)
over the l with no no-good; lex order is compatible with vector addition."
  (let ((best (loop for l below (first (chain-labels chain))
                    collect (chain-unary-costs chain 0 l))))
    (loop for p from 1 below (length (chain-labels chain))
          do (setf best
                   (loop for m below (nth p (chain-labels chain))
                         collect (let ((options
                                         (loop for b in best for l from 0
                                               when (and b (not (chain-nogood-p chain (1- p) l m)))
                                                 collect (%v+ (%v+ b (chain-pair-costs chain (1- p) l m))
                                                              (chain-unary-costs chain p m)))))
                                   (and options (lex-min options))))))
    (let ((finals (remove nil best)))
      (and finals (lex-min finals)))))

(defun chain-labellings (chain)
  "Every labelling (list of one label per position), feasible or not."
  (let ((result (list nil)))
    (dolist (n (reverse (chain-labels chain)) result)
      (setf result (loop for l below n nconc (mapcar (lambda (rest) (cons l rest)) result))))))

(defun chain-labelling-cost (chain labelling)
  "Cost vector of LABELLING, or NIL when it hits a no-good."
  (let ((total (%zero chain)))
    (loop for (l . more) on labelling for p from 0
          do (setf total (%v+ total (chain-unary-costs chain p l)))
             (when more
               (let ((m (first more)))
                 (when (chain-nogood-p chain p l m) (return-from chain-labelling-cost nil))
                 (setf total (%v+ total (chain-pair-costs chain p l m))))))
    total))

(defun chain-brute (chain)
  "CHAIN-DP by enumeration (checks the oracle itself)."
  (let ((costs (remove nil (mapcar (lambda (lab) (chain-labelling-cost chain lab))
                                   (chain-labellings chain)))))
    (and costs (lex-min costs))))

(defun chain-model (chain labelling)
  "The complete model of LABELLING: x(p,l) true for the chosen labels, y true
exactly for the chosen adjacent pairs (the cheapest completion)."
  (append
   (loop for p from 0 for n in (chain-labels chain)
         nconc (loop for l below n collect (cons (chain-x p l) (= l (nth p labelling)))))
   (loop for ((p l m)) in (chain-pair chain)
         collect (cons (chain-y p l m) (and (= l (nth p labelling)) (= m (nth (1+ p) labelling)))))))

(defun chain-model-labelling (chain model)
  "The labelling MODEL chooses, or :INVALID when a position does not have exactly
one label or a no-good holds."
  (let ((labelling
          (loop for p from 0 for n in (chain-labels chain)
                collect (let ((chosen (loop for l below n
                                            when (cdr (assoc (chain-x p l) model :test #'equal))
                                              collect l)))
                          (if (= 1 (length chosen))
                              (first chosen)
                              (return-from chain-model-labelling :invalid))))))
    (if (chain-labelling-cost chain labelling) labelling :invalid)))

(defun chain-worst-labelling (chain)
  "A feasible labelling of the greatest cost (lexicographically), or NIL."
  (let ((best nil) (best-cost nil))
    (dolist (lab (chain-labellings chain) best)
      (let ((c (chain-labelling-cost chain lab)))
        (when (and c (or (null best-cost) (lex< best-cost c)))
          (setf best lab best-cost c))))))

(defun random-chains (seed count &rest keys)
  "COUNT chains from SEED (keys as RANDOM-CHAIN)."
  (let ((rng (make-rng seed)))
    (loop repeat count collect (apply #'random-chain rng keys))))
