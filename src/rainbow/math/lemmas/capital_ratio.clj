(ns rainbow.math.lemmas.capital-ratio
  "General lemmas: capital ratio. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(def falsity (f/const* 'proposition/falsity []))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn rwa [w E n] (sum (f/lam [['rw-i nat]] (mul (at w 'rw-i) (at E 'rw-i))) n))

(def exposure-spec
  (let [E 'ex-e w 'ex-w n 'ex-n SE (sum E n) R (rwa w E n)
        WE (f/lam [['rw-i nat]] (mul (at w 'rw-i) (at E 'rw-i)))
        Z (f/lam [['ex-z nat]] s/zero)
        se-nn (call 'signed/expr-sum-value-nonnegative E n 'ex-hE)
        none (f/lam [['ex-le (le SE s/zero)]]
                    (let [each (call 'signed/expr-sum-value-nonnegative-terms-zero E n 'ex-hE (anti SE s/zero 'ex-le se-nn))
                          r0 (a/chain R [(sum Z n) (a/sum-cong WE Z n 'ex-c
                                                               (fn [i hi] (a/chain (mul (at w i) (at E i))
                                                                                   [(mul (at w i) s/zero) (mcong (at w i) (at w i) (at E i) s/zero (refl (at w i)) (at each i hi))]
                                                                                   [s/zero (call 'signed/multiply-zero-right (at w i))])))]
                                      [s/zero (call 'signed/expr-sum-value-zero n)])]
                      (call 'signed/less-than-irreflexive s/zero
                            (call 'signed/less-than-of-less-than-of-at-most s/zero R s/zero 'ex-pos (a/eq-le R s/zero r0)))))]
    (s/spec 'signed/exposure-positive
            [['ex-e family] ['ex-w family] ['ex-n nat]
             ['ex-hE (s/all-below n #(le s/zero (at E %)))]
             ['ex-hw (s/all-below n #(le s/zero (at w %)))]
             ['ex-pos (lt s/zero R)]]
            (lt s/zero SE)
            (call 'signed/less-than-intro s/zero SE se-nn
                  (f/lam [['ex-e0 (eqv s/zero SE)]] (f/app none (a/eq-le SE s/zero (sym s/zero SE 'ex-e0))))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(def theorem-specs [exposure-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-capital-ratio theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
