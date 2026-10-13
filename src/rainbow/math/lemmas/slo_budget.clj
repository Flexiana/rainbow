(ns rainbow.math.lemmas.slo-budget
  "General lemmas: slo budget. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn lt-le [x y h] (call 'signed/less-than-implies-at-most x y h))

(def compliance-spec
  (let [A 'sc-a tau 'sc-tau T 'sc-t E 'sc-e D (sub A tau)
        fwd (f/lam [['sc-le (le tau A)]]
                   (let [d-nn (le-resp (sub tau tau) s/zero (sub A tau) D (ring (sub tau tau) s/zero) (refl D)
                                       (call 'signed/add-right-monotone tau A (neg tau) 'sc-le))]
                     (le-resp (mul s/zero T) s/zero (mul D T) E (call 'signed/multiply-zero-left T) (sym E (mul D T) 'sc-he)
                              (call 'signed/multiply-right-monotone T s/zero D (lt-le s/zero T 'sc-pos) d-nn))))
        bwd (f/lam [['sc-e0 (le s/zero E)]]
                   (let [d-nn (call 'signed/at-most-cancel-positive-right s/zero D T 'sc-pos
                                    (le-resp s/zero (mul s/zero T) E (mul D T) (sym (mul s/zero T) s/zero (call 'signed/multiply-zero-left T)) 'sc-he 'sc-e0))]
                     (le-resp (add s/zero tau) tau (add D tau) A (ring (add s/zero tau) tau) (ring (add D tau) A)
                              (call 'signed/add-right-monotone s/zero D tau d-nn))))]
    (s/spec 'signed/slo-compliance
            [['sc-a signed] ['sc-tau signed] ['sc-t signed] ['sc-e signed] ['sc-pos (lt s/zero T)] ['sc-he (eqv E (mul D T))]]
            (pconj (f/arrow (le tau A) (le s/zero E)) (f/arrow (le s/zero E) (le tau A)))
            (conjoin (f/arrow (le tau A) (le s/zero E)) (f/arrow (le s/zero E) (le tau A)) fwd bwd))))

(defn budget [T D t] (sub (sub T D) (mul t T)))

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

(def theorem-specs [compliance-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-slo-budget theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
