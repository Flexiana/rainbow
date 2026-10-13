(ns rainbow.math.lemmas.sigtime-readings
  "General lemmas: sigtime readings. The mathematical facts the corresponding checks rest on,
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

(def bool (f/const* 'data/Bool []))

(def btrue (f/const* 'data/true []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn cases [p q r hpq hp hq] (call 'proposition/use-disjunction p q r hpq hp hq))

(def difference-positive-spec
  (let [l 'dp-l r 'dp-r D (call 'signed/decide-at-most r l) val (fn [c] (sel one s/zero c))
        d (add r (neg l))
        not-rl (f/lam [['dp-rl (le r l)]]
                      (call 'signed/one-not-at-most-zero
                            (f/app (f/const* 'equality/substitution [type-level]) bool D btrue
                                   (call 'signed/decide-at-most-true-complete r l 'dp-rl)
                                   (f/lam [['ct bool]] (le one (val 'ct))) 'dp-h)))
        not-le (f/lam [['dp-le (le d s/zero)]]
                      (f/app not-rl
                             (le-resp (add d l) r (add s/zero l) l (a/ring-eq (add d l) r) (a/ring-eq (add s/zero l) l)
                                      (call 'signed/add-right-monotone d s/zero l 'dp-le))))
        nonneg (cases (le s/zero d) (le d s/zero) (le s/zero d) (call 'signed/at-most-total s/zero d)
                      (f/lam [['dp-a (le s/zero d)]] 'dp-a)
                      (f/lam [['dp-b (le d s/zero)]] (call 'proposition/explode (le s/zero d) (f/app not-le 'dp-b))))]
    (s/spec 'signed/strict-indicator-difference-positive [['dp-l signed] ['dp-r signed] ['dp-h (le one (val D))]]
            (lt s/zero d)
            (call 'signed/less-than-intro s/zero d nonneg
                  (f/lam [['dp-e (eqv s/zero d)]] (f/app not-le (a/eq-le d s/zero (sym s/zero d 'dp-e))))))))

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

(def theorem-specs [difference-positive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-sigtime-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
