(ns rainbow.math.lemmas.credibility-readings
  "General lemmas: credibility readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(def between-spec
  (let [[Z W x u P] '[cb-z cb-w cb-x cb-u cb-p]
        mix (add (mul Z x) (mul W u))
        unit (fn [y] (a/chain (mul (add Z W) y) [(mul one y) (mcong (add Z W) one y y 'cb-s (refl y))] [y (call 'signed/multiply-one-left y)]))
        lo (le-resp (add (mul Z x) (mul W x)) x mix P
                    (trans (add (mul Z x) (mul W x)) (mul (add Z W) x) x (ring (add (mul Z x) (mul W x)) (mul (add Z W) x)) (unit x))
                    (sym P mix 'cb-h)
                    (call 'signed/add-left-monotone (mul W x) (mul W u) (mul Z x) (call 'signed/multiply-left-monotone W x u 'cb-hw 'cb-le)))
        hi (le-resp mix P (add (mul Z u) (mul W u)) u
                    (sym P mix 'cb-h)
                    (trans (add (mul Z u) (mul W u)) (mul (add Z W) u) u (ring (add (mul Z u) (mul W u)) (mul (add Z W) u)) (unit u))
                    (call 'signed/add-right-monotone (mul Z x) (mul Z u) (mul W u) (call 'signed/multiply-left-monotone Z x u 'cb-hz 'cb-le)))]
    (s/spec 'signed/convex-combination-between
            [['cb-z signed] ['cb-w signed] ['cb-x signed] ['cb-u signed] ['cb-p signed]
             ['cb-hz (le s/zero Z)] ['cb-hw (le s/zero W)] ['cb-s (eqv (add Z W) one)] ['cb-h (eqv P mix)] ['cb-le (le x u)]]
            (pconj (le x P) (le P u))
            (conjoin (le x P) (le P u) lo hi))))

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

(def theorem-specs [between-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-credibility-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
