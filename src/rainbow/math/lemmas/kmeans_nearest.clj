(ns rainbow.math.lemmas.kmeans-nearest
  "General lemmas: kmeans nearest. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.ufl-gap :as ufl]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn positive-part [t] (ufl/positive-part t))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def zero-one-nonneg-spec
  (let [goal (le s/zero 'x)]
    (s/spec 'signed/zero-one-nonnegative [['x signed] ['h (eqv (mul 'x (sub one 'x)) s/zero)]]
            goal
            (call 'proposition/use-disjunction (eqv 'x s/zero) (eqv (sub one 'x) s/zero) goal
                  (call 'signed/multiply-zero-split 'x (sub one 'x) 'h)
                  (f/lam [['hx (eqv 'x s/zero)]] (a/eq-le s/zero 'x (sym 'x s/zero 'hx)))
                  (f/lam [['h1 (eqv (sub one 'x) s/zero)]]
                         ;; x ~ 1 - (1 - x) ~ 1 - 0 ~ 1 >= 0
                         (le-resp s/zero s/zero one 'x (refl s/zero)
                                  (a/chain one [(sub one s/zero) (ring one (sub one s/zero))]
                                           [(sub one (sub one 'x)) (s/add-cong one one (neg s/zero) (neg (sub one 'x)) (refl one)
                                                                               (a/neg-cong s/zero (sub one 'x) (sym (sub one 'x) s/zero 'h1)))]
                                           ['x (ring (sub one (sub one 'x)) 'x)])
                                  (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one []))))))))

(defn worse [X d K j] (sum (f/lam [['wk nat]] (mul (at X 'wk) (positive-part (sub (at d 'wk) (at d j))))) K))

(defn nearest-sum [X d K] (sum (f/lam [['nj nat]] (worse X d K 'nj)) K))

(def nearest-spec
  (let [K 'K
        term (fn [k j] (mul (at 'X k) (positive-part (sub (at 'd k) (at 'd j)))))
        term-nonneg (fn [k j hk] (nonneg-prod (at 'X k) (positive-part (sub (at 'd k) (at 'd j))) (at 'x0 k hk)
                                              (call 'signed/positive-part-nonneg (sub (at 'd k) (at 'd j)))))
        worse-nonneg (fn [j] (call 'signed/expr-sum-value-nonnegative (f/lam [['wk nat]] (term 'wk j)) K
                                   (f/lam [['tk nat] ['tb (below 'tk K)]] (term-nonneg 'tk j 'tb))))
        W (f/lam [['nj nat]] (worse 'X 'd K 'nj))
        total-zero (call 'signed/at-most-antisymmetric (nearest-sum 'X 'd K) s/zero 'hnear
                         (call 'signed/expr-sum-value-nonnegative W K (f/lam [['oj nat] ['ob (below 'oj K)]] (worse-nonneg 'oj))))
        worse-zero (call 'signed/expr-sum-value-nonnegative-terms-zero W K
                         (f/lam [['oj nat] ['ob (below 'oj K)]] (worse-nonneg 'oj)) total-zero)
        term-zero (call 'signed/expr-sum-value-nonnegative-terms-zero (f/lam [['wk nat]] (term 'wk 'j)) K
                        (f/lam [['tk nat] ['tb (below 'tk K)]] (term-nonneg 'tk 'j 'tb))
                        (at worse-zero 'j 'hj))
        t (sub (at 'd 'k) (at 'd 'j)) pt (positive-part t)
        pos-zero (a/chain pt
                          [(mul one pt) (sym (mul one pt) pt (call 'signed/multiply-one-left pt))]
                          [(mul (at 'X 'k) pt) (a/mul-cong one (at 'X 'k) pt pt (sym (at 'X 'k) one 'hx) (refl pt))]
                          [s/zero (at term-zero 'k 'hk)])
        t-np (le-trans t pt s/zero (call 'signed/positive-part-upper t) (a/eq-le pt s/zero pos-zero))]
    (s/spec 'signed/kmeans-assigned-is-nearest
            [['X family] ['d family] ['K nat]
             ['x0 (s/all-below K #(le s/zero (at 'X %)))] ['hnear (le (nearest-sum 'X 'd K) s/zero)]
             ['k nat] ['hk (below 'k K)] ['hx (eqv (at 'X 'k) one)] ['j nat] ['hj (below 'j K)]]
            (le (at 'd 'k) (at 'd 'j))
            (call 'signed/add-of-at-most-subtract-local (at 'd 'j) (at 'd 'k) t-np))))

(def rearrange-spec
  (s/spec 'signed/add-of-at-most-subtract-local [['dj signed] ['dk signed] ['h (le (sub 'dk 'dj) s/zero)]]
          (le 'dk 'dj)
          (le-resp (add (sub 'dk 'dj) 'dj) 'dk (add s/zero 'dj) 'dj
                   (ring (add (sub 'dk 'dj) 'dj) 'dk) (ring (add s/zero 'dj) 'dj)
                   (call 'signed/add-right-monotone (sub 'dk 'dj) s/zero 'dj 'h))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [zero-one-nonneg-spec rearrange-spec nearest-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      ufl/extend-environment
      rectangular-index/extend-environment
      pairs/extend-environment
      positivity/extend-environment
      (support/extend-with :expr-sum-kmeans-nearest theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
