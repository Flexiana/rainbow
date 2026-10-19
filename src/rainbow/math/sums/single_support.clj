(ns rainbow.math.sums.single-support
  "Single supported terms and tight finite unit-capacity sums."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.one-hot-index :as hot] [rainbow.math.sums.of-nat :as on]
            [rainbow.math.nat.pigeonhole :as pigeon]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def below-distinct-spec
  (s/spec 'nat/below-implies-distinct [['i nat] ['j nat] ['below (s/below 'i 'j)]] (hot/notp (a/enat 'i 'j))
    (f/lam [['equal (a/enat 'i 'j)]]
      (call 'nat/not-strictly-below-self 'j
        (a/nsubst 'i 'j 'equal (f/lam [['index nat]] (s/below 'index 'j)) 'below)))))
(defn support-at [F n i]
  (let [j (gensym "index") h (gensym "bound") d (gensym "distinct")]
    (f/forall [[j nat] [h (s/below j n)] [d (hot/notp (a/enat j i))]] (eqv (at F j) s/zero))))
(def single-spec
  (let [F 'F i 'i n 'n claim (fn [k] (f/forall [['bound (s/below i k)] ['support (support-at F k i)]] (eqv (sum F k) (at F i))))
        Z (f/lam [['ignored nat]] s/zero)]
    (s/spec 'signed/expr-sum-single-support [[F family] [i nat] [n nat]] (claim n)
      (s/induct claim
        (f/lam [['bound (s/below i s/nz)] ['support (support-at F s/nz i)]]
          (#'pigeon/below-zero-absurd i 'bound (eqv (sum F s/nz) (at F i))))
        (fn [q ih]
          (let [goal (eqv (sum F (s/succ q)) (at F i))
                prefix-zero
                (s/trans (sum F q) (sum Z q) s/zero
                  (a/sum-cong F Z q 'j
                    (fn [j hj]
                      (at 'support j (s/weaken j q hj)
                        (f/lam [['ji (a/enat j i)]]
                          (at (call 'nat/below-implies-distinct j q hj) (a/nt j i q 'ji 'last))))))
                  (call 'signed/expr-sum-value-zero q))
                last-equal (a/nsubst q i (a/nsym i q 'last) (f/lam [['index nat]] (eqv (at F q) (at F 'index))) (refl (at F q)))
                prefix-support (let [j (gensym "index") hj (gensym "bound") d (gensym "distinct")]
                                 (f/lam [[j nat] [hj (s/below j q)] [d (hot/notp (a/enat j i))]] (at 'support j (s/weaken j q hj) d)))
                last-zero (at 'support q (s/self-below q)
                            (f/lam [['qi (a/enat q i)]]
                              (at (call 'nat/below-implies-distinct i q 'earlier) (a/nsym q i 'qi))))]
            (f/lam [['bound (s/below i (s/succ q))] ['support (support-at F (s/succ q) i)]]
              (a/cases (a/enat i q) (s/below i q) goal
                (call 'nat/at-most-split i q (call 'nat/at-most-successor-cancel-local i q 'bound))
                (f/lam [['last (a/enat i q)]]
                  (a/chain (sum F (s/succ q))
                    [(add s/zero (at F q)) (s/add-cong (sum F q) s/zero (at F q) (at F q) prefix-zero (refl (at F q)))]
                    [(at F q) (a/ring-eq (add s/zero (at F q)) (at F q))]
                    [(at F i) last-equal]))
                (f/lam [['earlier (s/below i q)]]
                  (a/chain (sum F (s/succ q))
                    [(add (at F i) s/zero) (s/add-cong (sum F q) (at F i) (at F q) s/zero (at ih 'earlier prefix-support) last-zero)]
                    [(at F i) (a/ring-eq (add (at F i) s/zero) (at F i))])))))) n))))
(def other-zero-spec
  (let [F 'F n 'n i 'i j 'j x (at F i) y (at F j) total (sum F n) goal (eqv y s/zero)
        conclude (fn [pair-bound]
                   (let [bound (s/le-transport (add x y) (add b/one y) total (add b/one s/zero)
                                 (s/add-cong x b/one y y 'selected (refl y))
                                 (s/trans total b/one (add b/one s/zero) 'unit (s/sym (add b/one s/zero) b/one (call 'signed/add-zero-right b/one))) pair-bound)]
                     (call 'signed/at-most-antisymmetric y s/zero
                       (call 'signed/at-most-add-left-cancel y s/zero b/one bound) (at 'nonnegative j 'hj))))]
    (s/spec 'signed/unit-mass-selected-others-zero
      [[F family] [n nat] ['nonnegative (s/all-below n #(le s/zero (at F %)))] ['unit (eqv total b/one)]
       [i nat] ['hi (s/below i n)] ['selected (eqv x b/one)] [j nat] ['hj (s/below j n)] ['distinct (hot/notp (a/enat i j))]] goal
      (a/cases (s/below i j) (a/disj (a/enat i j) (s/below j i)) goal (call 'nat/trichotomy i j)
        (f/lam [['ij (s/below i j)]] (conclude (call 'signed/two-terms-below-sum F n 'nonnegative i j 'ij 'hj)))
        (f/lam [['other (a/disj (a/enat i j) (s/below j i))]]
          (a/cases (a/enat i j) (s/below j i) goal 'other
            (f/lam [['equal (a/enat i j)]] (call 'proposition/explode goal (at 'distinct 'equal)))
            (f/lam [['ji (s/below j i)]]
              (conclude (s/le-transport (add y x) (add x y) total total (call 'signed/add-commutative y x) (refl total)
                          (call 'signed/two-terms-below-sum F n 'nonnegative j i 'ji 'hi))))))))))
(defn complements [F] (let [i (gensym "index")] (f/lam [[i nat]] (a/sub b/one (at F i)))))
(def complement-sum-spec
  (let [F 'F n 'n G (complements F) C (f/lam [['ignored nat]] b/one)
        T (f/lam [['i nat]] (add (at G 'i) (at F 'i)))
        SG (sum G n) SF (sum F n) count (on/of-nat n)
        total (a/chain (add SG SF)
                [(sum T n) (s/sym (sum T n) (add SG SF) (call 'signed/expr-sum-value-add G F n))]
                [(sum C n) (a/sum-cong T C n 'i (fn [i _] (a/ring-eq (add (a/sub b/one (at F i)) (at F i)) b/one)))]
                [(s/mul b/one count) (call 'signed/expr-sum-constant-of-nat b/one n)]
                [count (call 'signed/multiply-one-left count)])]
    (s/spec 'signed/expr-sum-complements [[F family] [n nat]] (eqv SG (a/sub count SF))
      (a/chain SG
        [(a/sub (add SG SF) SF) (a/ring-eq SG (a/sub (add SG SF) SF))]
        [(a/sub count SF) (s/add-cong (add SG SF) count (a/neg SF) (a/neg SF) total (refl (a/neg SF)))]))))
(def saturated-spec
  (let [F 'F q 'q n (s/succ q) i 'i j 'j G (complements F) count (on/of-nat q)
        total (a/chain (sum G n)
                [(a/sub (on/of-nat n) (sum F n)) (call 'signed/expr-sum-complements F n)]
                [(a/sub (add count b/one) count)
                 (s/add-cong (on/of-nat n) (add count b/one) (a/neg (sum F n)) (a/neg count)
                   (call 'signed/of-nat-successor q) (a/neg-cong (sum F n) count 'total))]
                [b/one (a/ring-eq (a/sub (add count b/one) count) b/one)])
        nn (f/lam [['index nat] ['bound (s/below 'index n)]]
             (call 'signed/order-implies-nonnegative-difference (at F 'index) b/one (at 'upper 'index 'bound)))
        selected (s/trans (at G i) (a/sub b/one s/zero) b/one
                   (s/add-cong b/one b/one (a/neg (at F i)) (a/neg s/zero) (refl b/one) (a/neg-cong (at F i) s/zero 'zero))
                   (a/ring-eq (a/sub b/one s/zero) b/one))
        gj0 (call 'signed/unit-mass-selected-others-zero G n nn total i 'hi selected j 'hj 'distinct)]
    (s/spec 'signed/all-but-one-unit-capacity-saturated
      [[F family] [q nat] ['upper (s/all-below n #(le (at F %) b/one))] ['total (eqv (sum F n) count)]
       [i nat] ['hi (s/below i n)] ['zero (eqv (at F i) s/zero)] [j nat] ['hj (s/below j n)] ['distinct (hot/notp (a/enat i j))]]
      (eqv (at F j) b/one)
      (s/sym b/one (at F j)
        (a/chain b/one
          [(add (at G j) (at F j)) (a/ring-eq b/one (add (a/sub b/one (at F j)) (at F j)))]
          [(add s/zero (at F j)) (s/add-cong (at G j) s/zero (at F j) (at F j) gj0 (refl (at F j)))]
          [(at F j) (a/ring-eq (add s/zero (at F j)) (at F j))])))))
(def count-except-spec
  (let [F 'F q 'q n (s/succ q) i 'i G (complements F) count (on/of-nat q)
        support (let [j (gensym "index") h (gensym "bound") d (gensym "distinct")]
                  (f/lam [[j nat] [h (s/below j n)] [d (hot/notp (a/enat j i))]]
                    (a/chain (at G j)
                      [(a/sub b/one b/one)
                       (s/add-cong b/one b/one (a/neg (at F j)) (a/neg b/one) (refl b/one)
                         (a/neg-cong (at F j) b/one (at 'others j h d)))]
                      [s/zero (a/ring-eq (a/sub b/one b/one) s/zero)])))
        single (call 'signed/expr-sum-single-support G i n 'hi support)
        unit (a/chain (sum G n)
               [(at G i) single]
               [(a/sub b/one s/zero)
                (s/add-cong b/one b/one (a/neg (at F i)) (a/neg s/zero) (refl b/one) (a/neg-cong (at F i) s/zero 'zero))]
               [b/one (a/ring-eq (a/sub b/one s/zero) b/one)])
        complement (call 'signed/expr-sum-complements F n)
        sf (sum F n)]
    (s/spec 'signed/all-but-one-ones-sum
      [[F family] [q nat] [i nat] ['hi (s/below i n)] ['zero (eqv (at F i) s/zero)]
       ['others (let [j (gensym "index") h (gensym "bound") d (gensym "distinct")]
                  (f/forall [[j nat] [h (s/below j n)] [d (hot/notp (a/enat j i))]] (eqv (at F j) b/one)))]]
      (eqv sf count)
      (a/chain sf
        [(a/sub (on/of-nat n) (a/sub (on/of-nat n) sf)) (a/ring-eq sf (a/sub (on/of-nat n) (a/sub (on/of-nat n) sf)))]
        [(a/sub (on/of-nat n) b/one)
         (s/add-cong (on/of-nat n) (on/of-nat n) (a/neg (a/sub (on/of-nat n) sf)) (a/neg b/one)
           (refl (on/of-nat n)) (a/neg-cong (a/sub (on/of-nat n) sf) b/one
             (s/trans (a/sub (on/of-nat n) sf) (sum G n) b/one (s/sym (sum G n) (a/sub (on/of-nat n) sf) complement) unit)))]
        [(a/sub (add count b/one) b/one)
         (s/add-cong (on/of-nat n) (add count b/one) (a/neg b/one) (a/neg b/one) (call 'signed/of-nat-successor q) (refl (a/neg b/one)))]
        [count (a/ring-eq (a/sub (add count b/one) b/one) count)]))))
(def theorem-specs [below-distinct-spec single-spec other-zero-spec complement-sum-spec saturated-spec count-except-spec])
(def deps '[rainbow.math.sums.one-hot-index rainbow.math.sums.of-nat rainbow.math.sums.nonblocking])
(defn install [env] (support/extend-with env :expr-sum-single-support theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.single-support))
