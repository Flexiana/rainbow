(ns rainbow.math.rational.signed.lp-duality
  "Linear-programming weak duality and the optimality certificate over SIGNED
  rationals -- arbitrary matrix, costs and right-hand side, any of them negative.

  For the program

      maximize    c . x
      subject to  (M x)_i <= b_i   for every row i,   x >= 0

  and a dual-feasible y >= 0 with c_j <= (M^T y)_j for every column j,

      optimization/signed-lp-weak-duality :  c . x  <=  b . y

  and, when a primal/dual pair closes the gap,

      optimization/signed-lp-optimality-certificate :
        b . y ~ c . x  ->  c . x' <= c . x  for every feasible x'

  so the pair is a machine-checkable proof that x is optimal, with no need to
  trust the solver that produced it.

  The existing nnrat LP stack proves the same statements only for NONNEGATIVE
  data, which excludes most real programs (costs to minimize, equality
  constraints split into two inequalities, any variable with a negative
  coefficient).  This is the general form.

  The argument is double counting on the term family

      T i j = (M i j * x j) * y i

  whose row totals are bounded by the primal constraints and whose column totals
  bound the dual objective:

    ROW     sum_j T i j ~ (M x)_i * y_i <= b_i * y_i     [scale-right, then
                                                          multiply-right-monotone
                                                          against y_i >= 0]
    COLUMN  c_j * x_j <= (M^T y)_j * x_j
                       ~ sum_i (M i j * y i) * x j
                       ~ sum_i (M i j * x j) * y i  =  sum_i T i j

  and `optimization/signed-double-counting-weak-duality` closes it with Fubini.
  The last step of the column bound is `signed/multiply-swap-outer`, which only
  became available with the nnrat-ring tactic.

  Native and axiom-free; chains the signed Fubini and associativity modules on
  D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.fubini :as fubini]
            [rainbow.math.rational.signed.multiply-associative :as assoc]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))
(defn- signed-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-multiply-right-monotone [c a b hc hab]
  (app (function/const* 'signed/multiply-right-monotone []) c a b hc hab))
(defn- signed-multiply-swap-outer [p q r]
  (app (function/const* 'signed/multiply-swap-outer []) p q r))
(defn- signed-map-sum-scale-right [A f c xs]
  (app (function/const* 'signed/map-sum-scale-right [U]) A f c xs))
(defn- signed-map-sum-respects [A f g hfg xs]
  (app (function/const* 'signed/map-sum-respects-equivalence [U]) A f g hfg xs))

;; ---- the column bound --------------------------------------------------------
;;
;; Reading coeff i = M i j, weights i = y i, scalar = x j, cost = c j, this says
;; the dual feasibility of one column, scaled by a nonnegative primal variable,
;; is below that column's total of the double-counting term family.

(def column-bound-spec
  {:name 'optimization/signed-lp-column-bound :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['coeff (function/arrow 'A signed)]
     ['weights (function/arrow 'A signed)]
     ['scalar signed] ['cost signed]
     ['is (list-of 'A)]
     ['dual-feasible
      (sle 'cost (map-sum 'A (function/lam [['i 'A]]
                                           (smul (app 'coeff 'i)
                                                 (app 'weights 'i))) 'is))]
     ['nonnegative (sle signed-zero 'scalar)]]
    (sle (smul 'cost 'scalar)
         (map-sum 'A (function/lam [['i 'A]]
                                   (smul (smul (app 'coeff 'i) 'scalar)
                                         (app 'weights 'i))) 'is)))
   :value
   (function/lam
    [['A type-u]
     ['coeff (function/arrow 'A signed)]
     ['weights (function/arrow 'A signed)]
     ['scalar signed] ['cost signed]
     ['is (list-of 'A)]
     ['dual-feasible
      (sle 'cost (map-sum 'A (function/lam [['i 'A]]
                                           (smul (app 'coeff 'i)
                                                 (app 'weights 'i))) 'is))]
     ['nonnegative (sle signed-zero 'scalar)]]
    (let [paired (function/lam [['i 'A]]
                               (smul (app 'coeff 'i) (app 'weights 'i)))
          scaled (function/lam [['i 'A]]
                               (smul (smul (app 'coeff 'i) (app 'weights 'i))
                                     'scalar))
          swapped (function/lam [['i 'A]]
                                (smul (smul (app 'coeff 'i) 'scalar)
                                      (app 'weights 'i)))
          total (map-sum 'A paired 'is)
          ;; (sum_i coeff_i * weights_i) * scalar ~ sum_i (coeff_i * scalar) * weights_i
          pulled
          (signed-trans
           (smul total 'scalar)
           (map-sum 'A scaled 'is)
           (map-sum 'A swapped 'is)
           (signed-map-sum-scale-right 'A paired 'scalar 'is)
           (signed-map-sum-respects
            'A scaled swapped
            (function/lam [['i 'A]]
                          (signed-multiply-swap-outer (app 'coeff 'i)
                                                      (app 'weights 'i)
                                                      'scalar))
            'is))]
      (signed-at-most-respects
       (smul 'cost 'scalar) (smul 'cost 'scalar)
       (smul total 'scalar) (map-sum 'A swapped 'is)
       (signed-refl (smul 'cost 'scalar))
       pulled
       (signed-multiply-right-monotone 'scalar 'cost total
                                       'nonnegative 'dual-feasible))))})

;; ---- weak duality ------------------------------------------------------------

(defn- constraint-row [M x cols i]
  (map-sum 'B (function/lam [['j 'B]]
                            (smul (app (app M i) 'j) (app x 'j))) cols))

(defn- dual-column [M y rows j]
  (map-sum 'A (function/lam [['i 'A]]
                            (smul (app (app M 'i) j) (app y 'i))) rows))

(def matrix-type (function/arrow 'A (function/arrow 'B signed)))

(defn- lp-bindings []
  [['A type-u] ['B type-u]
   ['M matrix-type]
   ['b (function/arrow 'A signed)]
   ['c (function/arrow 'B signed)]
   ['x (function/arrow 'B signed)]
   ['y (function/arrow 'A signed)]
   ['rows (list-of 'A)] ['cols (list-of 'B)]
   ['primal-feasible
    (function/forall [['i 'A]] (sle (constraint-row 'M 'x 'cols 'i) (app 'b 'i)))]
   ['dual-feasible
    (function/forall [['j 'B]] (sle (app 'c 'j) (dual-column 'M 'y 'rows 'j)))]
   ['x-nonnegative
    (function/forall [['j 'B]] (sle signed-zero (app 'x 'j)))]
   ['y-nonnegative
    (function/forall [['i 'A]] (sle signed-zero (app 'y 'i)))]])

(def ^:private primal-objective
  (map-sum 'B (function/lam [['j 'B]] (smul (app 'c 'j) (app 'x 'j))) 'cols))
(def ^:private dual-objective
  (map-sum 'A (function/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i))) 'rows))

;; T i j = (M i j * x j) * y i
(def ^:private term-family
  (function/lam
   [['i 'A]]
   (function/lam [['j 'B]]
                 (smul (smul (app (app 'M 'i) 'j) (app 'x 'j)) (app 'y 'i)))))

(def ^:private weak-duality-body
  (app (function/const* 'optimization/signed-double-counting-weak-duality [U])
       'A 'B term-family
       (function/lam [['j 'B]] (smul (app 'c 'j) (app 'x 'j)))
       (function/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i)))
       'rows 'cols
       ;; column: c_j * x_j <= sum_i T i j
       (function/lam
        [['j 'B]]
        (app (function/const* 'optimization/signed-lp-column-bound [U])
             'A
             (function/lam [['i 'A]] (app (app 'M 'i) 'j))
             'y (app 'x 'j) (app 'c 'j) 'rows
             (app 'dual-feasible 'j)
             (app 'x-nonnegative 'j)))
       ;; row: sum_j T i j <= b_i * y_i
       (function/lam
        [['i 'A]]
        (app (function/const*
              'optimization/signed-row-bound-of-primal-feasibility [U])
             'B
             (function/lam [['j 'B]]
                           (smul (app (app 'M 'i) 'j) (app 'x 'j)))
             (app 'b 'i) (app 'y 'i) 'cols
             (app 'primal-feasible 'i)
             (app 'y-nonnegative 'i)))))

(def weak-duality-spec
  {:name 'optimization/signed-lp-weak-duality :universes ['u]
   :type (function/forall (lp-bindings) (sle primal-objective dual-objective))
   :value (function/lam (lp-bindings) weak-duality-body)})

;; ---- the optimality certificate ----------------------------------------------

(def optimality-certificate-spec
  {:name 'optimization/signed-lp-optimality-certificate :universes ['u]
   :type
   (function/forall
    (into (lp-bindings)
          [['gap (seq-equiv dual-objective primal-objective)]
           ['candidate (function/arrow 'B signed)]
           ['candidate-feasible
            (function/forall [['i 'A]]
                             (sle (constraint-row 'M 'candidate 'cols 'i)
                                  (app 'b 'i)))]
           ['candidate-nonnegative
            (function/forall [['j 'B]] (sle signed-zero (app 'candidate 'j)))]])
    (sle (map-sum 'B (function/lam [['j 'B]]
                                   (smul (app 'c 'j) (app 'candidate 'j)))
                  'cols)
         primal-objective))
   :value
   (function/lam
    (into (lp-bindings)
          [['gap (seq-equiv dual-objective primal-objective)]
           ['candidate (function/arrow 'B signed)]
           ['candidate-feasible
            (function/forall [['i 'A]]
                             (sle (constraint-row 'M 'candidate 'cols 'i)
                                  (app 'b 'i)))]
           ['candidate-nonnegative
            (function/forall [['j 'B]] (sle signed-zero (app 'candidate 'j)))]])
    (let [candidate-objective
          (map-sum 'B (function/lam [['j 'B]]
                                    (smul (app 'c 'j) (app 'candidate 'j)))
                   'cols)]
      ;; weak duality bounds the candidate by the shared dual objective, and the
      ;; gap identifies that with the incumbent's objective
      (signed-at-most-respects
       candidate-objective candidate-objective
       dual-objective primal-objective
       (signed-refl candidate-objective)
       'gap
       (app (function/const* 'optimization/signed-lp-weak-duality [U])
            'A 'B 'M 'b 'c 'candidate 'y 'rows 'cols
            'candidate-feasible 'dual-feasible
            'candidate-nonnegative 'y-nonnegative))))})

(def definition-specs [])
(def theorem-specs
  [column-bound-spec weak-duality-spec optimality-certificate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      fubini/extend-environment
      assoc/extend-environment
      (support/extend-with :signed-lp-duality theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
