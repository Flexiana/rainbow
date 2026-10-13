(ns rainbow.math.sums.nonneg-zero
  "Nonnegative terms that sum to zero are each zero, over signed/expr-sum-value: if 0 <= F i for every
  i < k and sum F k ~ 0 then F i ~ 0 for every i < k. The two-term step: 0 <= a, 0 <= b, a + b ~ 0
  give a ~ 0 (a <= a + b ~ 0 and 0 <= a) and then b ~ 0. The induction peels the last term."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.order-monotone :as monotone]
            [rainbow.math.nat.infinite :as infinite]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.algorithms.proofs.graph.walk-shorten :as shorten]))

(defn- add [x y] (call 'signed/add x y))
(defn- le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))
(defn- le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))
(defn- both [l r lp rp] (call 'proposition/conjoin l r lp rp))

;; 0 <= a, 0 <= b, a + b ~ 0  ->  a ~ 0 /\ b ~ 0
(def pair-spec
  (let [ab (add 'a 'b)
        ;; a = a + 0 <= a + b ~ 0
        a-np (le-trans 'a ab s/zero
                       (le-resp (add 'a s/zero) 'a ab ab (a/ring-eq (add 'a s/zero) 'a) (refl ab)
                                (call 'signed/add-left-monotone s/zero 'b 'a 'hb))
                       (a/eq-le ab s/zero 'hab))
        b-np (le-trans 'b ab s/zero
                       (le-resp (add s/zero 'b) 'b ab ab (a/ring-eq (add s/zero 'b) 'b) (refl ab)
                                (call 'signed/add-right-monotone s/zero 'a 'b 'ha))
                       (a/eq-le ab s/zero 'hab))]
    (s/spec 'signed/nonnegative-pair-sum-zero
            [['a signed] ['b signed] ['ha (le s/zero 'a)] ['hb (le s/zero 'b)] ['hab (eqv ab s/zero)]]
            (call 'proposition/conjunction (eqv 'a s/zero) (eqv 'b s/zero))
            (both (eqv 'a s/zero) (eqv 'b s/zero)
                  (call 'signed/at-most-antisymmetric 'a s/zero a-np 'ha)
                  (call 'signed/at-most-antisymmetric 'b s/zero b-np 'hb)))))

;; 0 <= sum F q for nonnegative F (needed for the induction step's first summand).
(def sum-nonneg-spec
  (let [Z (f/lam [['zi nat]] s/zero)]
    (s/spec 'signed/expr-sum-value-nonnegative
            [['F family] ['k nat] ['hF (s/all-below 'k #(le s/zero (at 'F %)))]]
            (le s/zero (sum 'F 'k))
            (le-resp (sum Z 'k) s/zero (sum 'F 'k) (sum 'F 'k) (call 'signed/expr-sum-value-zero 'k) (refl (sum 'F 'k))
                     (call 'signed/expr-sum-value-monotone-below Z 'F 'k 'hF)))))

(def terms-zero-spec
  (let [claim (fn [k] (f/forall [['hF (s/all-below k #(le s/zero (at 'F %)))] ['hs (eqv (sum 'F k) s/zero)]]
                                (s/all-below k #(eqv (at 'F %) s/zero))))]
    (s/spec 'signed/expr-sum-value-nonnegative-terms-zero [['F family] ['k nat]] (claim 'k)
            (s/induct claim
                      ;; k = 0: nothing below 0 -- vacuous; use the bound to derive falsity
                      (f/lam [['hF (s/all-below s/nz #(le s/zero (at 'F %)))] ['hs (eqv (sum 'F s/nz) s/zero)]
                              ['idx nat] ['bound (below 'idx s/nz)]]
                             (call 'proposition/explode (eqv (at 'F 'idx) s/zero)
                                   (at (call 'nat/zero-not-successor 'idx)
                                       (f/app (f/const* 'equality/symmetric [[:succ [:zero]]]) nat (s/succ 'idx) s/nz
                                              (call 'nat/equal-zero-of-at-most-zero (s/succ 'idx) 'bound)))))
                      (fn [q ih]
                        (let [head (sum 'F q) last-term (at 'F q)]
                          (f/lam [['hF (s/all-below (s/succ q) #(le s/zero (at 'F %)))] ['hs (eqv (sum 'F (s/succ q)) s/zero)]]
                                 (let [hF-q (f/lam [['pi nat] ['pb (below 'pi q)]]
                                                   (at 'hF 'pi (s/weaken 'pi q 'pb)))
                                       pair (call 'signed/nonnegative-pair-sum-zero head last-term
                                                  (call 'signed/expr-sum-value-nonnegative 'F q hF-q)
                                                  (at 'hF q (s/self-below q)) 'hs)
                                       head-zero (call 'proposition/left (eqv head s/zero) (eqv last-term s/zero) pair)
                                       last-zero (call 'proposition/right (eqv head s/zero) (eqv last-term s/zero) pair)
                                       below-q (at ih hF-q head-zero)]
                                   (f/lam [['idx nat] ['bound (below 'idx (s/succ q))]]
                                          (call 'proposition/use-disjunction
                                                (f/equality [:succ [:zero]] nat 'idx q) (below 'idx q) (eqv (at 'F 'idx) s/zero)
                                                (call 'nat/at-most-split 'idx q (call 'nat/at-most-successor-cancel-local 'idx q 'bound))
                                                (f/lam [['he (f/equality [:succ [:zero]] nat 'idx q)]]
                                                       (f/app (f/const* 'equality/substitution [[:succ [:zero]]]) nat q 'idx
                                                              (f/app (f/const* 'equality/symmetric [[:succ [:zero]]]) nat 'idx q 'he)
                                                              (f/lam [['p nat]] (eqv (at 'F 'p) s/zero)) last-zero))
                                                (f/lam [['hl (below 'idx q)]] (at below-q 'idx 'hl))))))))
                      'k))))

(def theorem-specs [pair-spec sum-nonneg-spec terms-zero-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env s/extend-environment a/extend-environment monotone/extend-environment infinite/extend-environment divmod/extend-environment shorten/extend-environment (support/extend-with :expr-sum-nonneg-zero theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.nonneg-zero))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
