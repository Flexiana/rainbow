(ns rainbow.math.lemmas.cashbudget-balance
  "General lemmas: cashbudget balance. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn closed-form [Cn C0 Bn B0 SR SP I] (add (add (add C0 (add SR (neg SP))) (add Bn (neg B0))) (neg I)))

(def closed-form-spec
  (let [[Cn C0 Bn B0 SP SY SI SR SD I] '[cf-cn cf-c0 cf-bn cf-b0 cf-sp cf-sy cf-si cf-sr cf-sd cf-i]
        X (add SP (add SY SI)) SD' (add (add Bn SY) (neg B0))
        sd (a/chain SD [(add (add B0 SD) (neg B0)) (ring SD (add (add B0 SD) (neg B0)))]
                    [SD' (acong (add B0 SD) (add Bn SY) (neg B0) (neg B0) (sym (add Bn SY) (add B0 SD) 'cf-hb) (refl (neg B0)))])
        A (add (add C0 (add SR (neg SP))) (add Bn (neg B0)))]
    (s/spec 'signed/cash-closed-form
            [['cf-cn signed] ['cf-c0 signed] ['cf-bn signed] ['cf-b0 signed] ['cf-sp signed] ['cf-sy signed] ['cf-si signed]
             ['cf-sr signed] ['cf-sd signed] ['cf-i signed]
             ['cf-hc (eqv (add Cn X) (add C0 (add SR SD)))] ['cf-hb (eqv (add Bn SY) (add B0 SD))] ['cf-hi (eqv SI I)]]
            (eqv Cn (closed-form Cn C0 Bn B0 SR SP I))
            (a/chain Cn
                     [(add (add Cn X) (neg X)) (ring Cn (add (add Cn X) (neg X)))]
                     [(add (add C0 (add SR SD)) (neg X)) (acong (add Cn X) (add C0 (add SR SD)) (neg X) (neg X) 'cf-hc (refl (neg X)))]
                     [(add (add C0 (add SR SD')) (neg X))
                      (acong (add C0 (add SR SD)) (add C0 (add SR SD')) (neg X) (neg X)
                             (acong C0 C0 (add SR SD) (add SR SD') (refl C0) (acong SR SR SD SD' (refl SR) sd))
                             (refl (neg X)))]
                     [(add A (neg SI)) (ring (add (add C0 (add SR SD')) (neg X)) (add A (neg SI)))]
                     [(add A (neg I)) (acong A A (neg SI) (neg I) (refl A) (a/neg-cong SI I 'cf-hi))]))))

(defn fam [g] (f/lam [['kf-t nat]] (g 'kf-t)))

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

(def theorem-specs [closed-form-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nat-more/extend-environment
      add-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-cashbudget-balance theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
