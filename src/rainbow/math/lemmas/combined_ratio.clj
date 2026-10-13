(ns rainbow.math.lemmas.combined-ratio
  "General lemmas: combined ratio. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn lt-le [x y h] (call 'signed/less-than-implies-at-most x y h))

(defn lt-neq [x y h] (call 'proposition/right (le x y) (f/arrow (eqv x y) falsity) h))

(defn no-pos-nonpos [U pos nonpos]
  (call 'signed/less-than-irreflexive s/zero (call 'signed/less-than-of-less-than-of-at-most s/zero U s/zero pos nonpos)))

(defn one-minus-times [c t]
  (a/chain (mul (sub one c) t)
           [(add (mul one t) (mul (neg c) t)) (call 'signed/multiply-distributes-add-right one (neg c) t)]
           [(sub t (mul c t)) (s/add-cong (mul one t) t (mul (neg c) t) (neg (mul c t)) (call 'signed/multiply-one-left t) (ring (mul (neg c) t) (neg (mul c t))))]))

(def profit-spec
  (let [C 'cp-c T 'cp-t U 'cp-u D (sub one C) DT (mul D T)
        ;; C < 1 -> 0 < 1 - C
        fwd (f/lam [['cp-lt (lt C one)]]
                   (let [d-nn (le-resp (sub C C) s/zero (sub one C) D (ring (sub C C) s/zero) (refl D)
                                       (call 'signed/add-right-monotone C one (neg C) (lt-le C one 'cp-lt)))
                         d-ne (f/lam [['cp-e (eqv s/zero D)]]
                                     (f/app (lt-neq C one 'cp-lt)
                                            (a/chain C [(add C s/zero) (ring C (add C s/zero))]
                                                     [(add C D) (s/add-cong C C s/zero D (refl C) 'cp-e)]
                                                     [one (ring (add C D) one)])))
                         d-pos (call 'signed/less-than-intro s/zero D d-nn d-ne)]
                     (call 'signed/less-than-of-less-than-of-at-most s/zero DT U
                           (call 'signed/multiply-positive D T d-pos 'cp-pos)
                           (a/eq-le DT U (sym U DT 'cp-hu)))))
        ;; 1 <= C -> U <= 0
        U-nonpos (fn [h1c]
                   (let [d-np (le-resp (sub one C) D (sub C C) s/zero (refl D) (ring (sub C C) s/zero)
                                       (call 'signed/add-right-monotone one C (neg C) h1c))]
                     (le-resp DT U (mul s/zero T) s/zero (sym U DT 'cp-hu) (call 'signed/multiply-zero-left T)
                              (call 'signed/multiply-right-monotone T D s/zero (lt-le s/zero T 'cp-pos) d-np))))
        bwd (f/lam [['cp-u0 (lt s/zero U)]]
                   (call 'signed/less-than-intro C one
                         (cases (le C one) (le one C) (le C one) (call 'signed/at-most-total C one)
                                (f/lam [['cp-a (le C one)]] 'cp-a)
                                (f/lam [['cp-b (le one C)]] (call 'proposition/explode (le C one) (no-pos-nonpos U 'cp-u0 (U-nonpos 'cp-b)))))
                         (f/lam [['cp-e (eqv C one)]] (no-pos-nonpos U 'cp-u0 (U-nonpos (a/eq-le one C (sym C one 'cp-e)))))))]
    (s/spec 'signed/combined-profit
            [['cp-c signed] ['cp-t signed] ['cp-u signed] ['cp-pos (lt s/zero T)] ['cp-hu (eqv U DT)]]
            (pconj (f/arrow (lt C one) (lt s/zero U)) (f/arrow (lt s/zero U) (lt C one)))
            (conjoin (f/arrow (lt C one) (lt s/zero U)) (f/arrow (lt s/zero U) (lt C one)) fwd bwd))))

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

(def theorem-specs [profit-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      multiply-positive/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      (support/extend-with-shared :expr-sum-combined-ratio theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
