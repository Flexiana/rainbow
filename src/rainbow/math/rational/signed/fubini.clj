(ns rainbow.math.rational.signed.fubini
  "Finite Fubini for signed sums, and the double-counting weak-duality theorem
  it powers.

    signed/map-sum-swap : sum_i sum_j T i j  ~  sum_j sum_i T i j

  Induction on the outer list: the empty case is a sum of empty sums, which
  `signed/map-sum-zero` collapses, and the cons step splits the inner sum with
  `signed/map-sum-add` and applies the induction hypothesis.

  The payoff is DOUBLE-COUNTING WEAK DUALITY.  Given a term family T i j (think
  T i j = A_ij x_j y_i), if every column's total dominates the primal
  contribution and every row's total is dominated by the dual contribution,

      c_j * x_j  <=  sum_i T i j          (each column)
      sum_j T i j  <=  b_i * y_i          (each row)

  then the primal objective is below the dual objective:

      sum_j c_j*x_j  <=  sum_i b_i*y_i.

  Summing the column bounds, swapping the order of summation, and applying the
  row bounds is the entire argument -- weak duality is double counting, and
  Fubini is the only nontrivial ingredient.  Unlike the nnrat LP stack this holds
  over SIGNED data, so the matrix, costs and right-hand side may all be negative.

  `optimization/signed-row-bound-of-primal-feasibility` discharges the row
  hypothesis from ordinary primal feasibility (Ax)_i <= b_i together with a
  nonnegative dual variable, by pulling y_i out of the row sum with
  `signed/map-sum-scale-right`.  The mirrored discharge of the column hypothesis
  additionally needs signed multiplicative associativity, which is not yet
  proved; callers supplying their own T must reassociate themselves.

  Native and axiom-free; chains the signed distributive toolkit on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as dist]))

(def zero-level [:zero])
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
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
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
(defn- signed-at-most-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-add-respects [a ah b bh same-a same-b]
  (app (function/const* 'signed/add-respects-equivalence [])
       a ah b bh same-a same-b))
(defn- signed-map-sum-monotone [A f g hfg xs]
  (app (function/const* 'signed/map-sum-monotone [U]) A f g hfg xs))
(defn- signed-map-sum-zero [A f hf xs]
  (app (function/const* 'signed/map-sum-zero [U]) A f hf xs))
(defn- signed-map-sum-add [A f g xs]
  (app (function/const* 'signed/map-sum-add [U]) A f g xs))
(defn- signed-map-sum-scale-right [A f c xs]
  (app (function/const* 'signed/map-sum-scale-right [U]) A f c xs))
(defn- signed-multiply-right-monotone [c a b hc hab]
  (app (function/const* 'signed/multiply-right-monotone []) c a b hc hab))

;; ---- Fubini ------------------------------------------------------------------

(def map-sum-swap-spec
  {:name 'signed/map-sum-swap :universes ['u]
   :type (function/forall
          [['A type-u] ['B type-u]
           ['T (function/arrow 'A (function/arrow 'B signed))]
           ['is (list-of 'A)] ['js (list-of 'B)]]
          (seq-equiv
           (map-sum 'A (function/lam
                        [['i 'A]]
                        (map-sum 'B (function/lam [['j 'B]]
                                                  (app (app 'T 'i) 'j)) 'js))
                    'is)
           (map-sum 'B (function/lam
                        [['j 'B]]
                        (map-sum 'A (function/lam [['i 'A]]
                                                  (app (app 'T 'i) 'j)) 'is))
                    'js)))
   :value
   (function/lam
    [['A type-u] ['B type-u]
     ['T (function/arrow 'A (function/arrow 'B signed))]
     ['is (list-of 'A)] ['js (list-of 'B)]]
    (app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam
      [['zs (list-of 'A)]]
      (seq-equiv
       (map-sum 'A (function/lam
                    [['i 'A]]
                    (map-sum 'B (function/lam [['j 'B]]
                                              (app (app 'T 'i) 'j)) 'js))
                'zs)
       (map-sum 'B (function/lam
                    [['j 'B]]
                    (map-sum 'A (function/lam [['i 'A]]
                                              (app (app 'T 'i) 'j)) 'zs))
                'js)))
     ;; nil : 0 ~ sum_j (empty inner sum) = sum_j 0
     (signed-sym
      (map-sum 'B (function/lam
                   [['j 'B]]
                   (map-sum 'A (function/lam [['i 'A]]
                                             (app (app 'T 'i) 'j))
                            (app (function/const* 'data/nil [data-level]) 'A)))
               'js)
      signed-zero
      (signed-map-sum-zero
       'B
       (function/lam
        [['j 'B]]
        (map-sum 'A (function/lam [['i 'A]] (app (app 'T 'i) 'j))
                 (app (function/const* 'data/nil [data-level]) 'A)))
       (function/lam [['j 'B]] (signed-refl signed-zero))
       'js))
     ;; cons head tail
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (seq-equiv
             (map-sum 'A (function/lam
                          [['i 'A]]
                          (map-sum 'B (function/lam [['j 'B]]
                                                    (app (app 'T 'i) 'j)) 'js))
                      'tail)
             (map-sum 'B (function/lam
                          [['j 'B]]
                          (map-sum 'A (function/lam [['i 'A]]
                                                    (app (app 'T 'i) 'j))
                                   'tail))
                      'js))]]
      (let [head-row (function/lam [['j 'B]] (app (app 'T 'head) 'j))
            tail-col (function/lam
                      [['j 'B]]
                      (map-sum 'A (function/lam [['i 'A]]
                                                (app (app 'T 'i) 'j)) 'tail))
            P (map-sum 'B head-row 'js)
            Q (map-sum 'B tail-col 'js)
            tail-rows (map-sum 'A (function/lam
                                   [['i 'A]]
                                   (map-sum 'B (function/lam
                                                [['j 'B]]
                                                (app (app 'T 'i) 'j)) 'js))
                               'tail)
            start (sadd P tail-rows)
            middle (sadd P Q)
            finish (map-sum 'B (function/lam
                                [['j 'B]]
                                (sadd (app head-row 'j) (app tail-col 'j)))
                            'js)]
        (signed-trans
         start middle finish
         (signed-add-respects P P tail-rows Q (signed-refl P) 'ih)
         (signed-sym finish middle
                     (signed-map-sum-add 'B head-row tail-col 'js)))))
     'is))})

;; ---- weak duality by double counting -----------------------------------------

(def double-counting-weak-duality-spec
  {:name 'optimization/signed-double-counting-weak-duality :universes ['u]
   :type
   (function/forall
    [['A type-u] ['B type-u]
     ['T (function/arrow 'A (function/arrow 'B signed))]
     ['primal (function/arrow 'B signed)] ['dual (function/arrow 'A signed)]
     ['is (list-of 'A)] ['js (list-of 'B)]
     ['column (function/forall
               [['j 'B]]
               (sle (app 'primal 'j)
                    (map-sum 'A (function/lam [['i 'A]]
                                              (app (app 'T 'i) 'j)) 'is)))]
     ['row (function/forall
            [['i 'A]]
            (sle (map-sum 'B (function/lam [['j 'B]]
                                           (app (app 'T 'i) 'j)) 'js)
                 (app 'dual 'i)))]]
    (sle (map-sum 'B 'primal 'js) (map-sum 'A 'dual 'is)))
   :value
   (function/lam
    [['A type-u] ['B type-u]
     ['T (function/arrow 'A (function/arrow 'B signed))]
     ['primal (function/arrow 'B signed)] ['dual (function/arrow 'A signed)]
     ['is (list-of 'A)] ['js (list-of 'B)]
     ['column (function/forall
               [['j 'B]]
               (sle (app 'primal 'j)
                    (map-sum 'A (function/lam [['i 'A]]
                                              (app (app 'T 'i) 'j)) 'is)))]
     ['row (function/forall
            [['i 'A]]
            (sle (map-sum 'B (function/lam [['j 'B]]
                                           (app (app 'T 'i) 'j)) 'js)
                 (app 'dual 'i)))]]
    (let [column-family (function/lam
                         [['j 'B]]
                         (map-sum 'A (function/lam [['i 'A]]
                                                   (app (app 'T 'i) 'j)) 'is))
          row-family (function/lam
                      [['i 'A]]
                      (map-sum 'B (function/lam [['j 'B]]
                                                (app (app 'T 'i) 'j)) 'js))
          columns-total (map-sum 'B column-family 'js)
          rows-total (map-sum 'A row-family 'is)
          ;; sum_j primal_j <= sum_j sum_i T i j
          below-columns
          (signed-map-sum-monotone 'B 'primal column-family 'column 'js)
          ;; sum_i sum_j T i j <= sum_i dual_i
          rows-below
          (signed-map-sum-monotone 'A row-family 'dual 'row 'is)
          ;; transport the column total to the row total by Fubini
          columns-below
          (signed-at-most-respects
           (map-sum 'B 'primal 'js) (map-sum 'B 'primal 'js)
           columns-total rows-total
           (signed-refl (map-sum 'B 'primal 'js))
           (signed-sym rows-total columns-total
                       (app (function/const* 'signed/map-sum-swap [U])
                            'A 'B 'T 'is 'js))
           below-columns)]
      (signed-at-most-transitive
       (map-sum 'B 'primal 'js) rows-total (map-sum 'A 'dual 'is)
       columns-below rows-below)))})

;; The row hypothesis follows from ordinary primal feasibility once the dual
;; variable is nonnegative: pull y_i out of the row sum, then scale the
;; feasibility inequality by it.
(def row-bound-spec
  {:name 'optimization/signed-row-bound-of-primal-feasibility :universes ['u]
   :type
   (function/forall
    [['B type-u]
     ['activity (function/arrow 'B signed)]
     ['bound signed] ['weight signed]
     ['js (list-of 'B)]
     ['feasible (sle (map-sum 'B 'activity 'js) 'bound)]
     ['nonnegative (sle signed-zero 'weight)]]
    (sle (map-sum 'B (function/lam [['j 'B]]
                                   (smul (app 'activity 'j) 'weight)) 'js)
         (smul 'bound 'weight)))
   :value
   (function/lam
    [['B type-u]
     ['activity (function/arrow 'B signed)]
     ['bound signed] ['weight signed]
     ['js (list-of 'B)]
     ['feasible (sle (map-sum 'B 'activity 'js) 'bound)]
     ['nonnegative (sle signed-zero 'weight)]]
    (let [total (map-sum 'B 'activity 'js)
          scaled (map-sum 'B (function/lam [['j 'B]]
                                           (smul (app 'activity 'j) 'weight))
                          'js)]
      (signed-at-most-respects
       (smul total 'weight) scaled
       (smul 'bound 'weight) (smul 'bound 'weight)
       (signed-map-sum-scale-right 'B 'activity 'weight 'js)
       (signed-refl (smul 'bound 'weight))
       (signed-multiply-right-monotone 'weight total 'bound
                                       'nonnegative 'feasible))))})

(def definition-specs [])
(def theorem-specs
  [map-sum-swap-spec double-counting-weak-duality-spec row-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-fubini theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.fubini))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
