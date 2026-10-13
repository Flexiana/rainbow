(ns rainbow.math.lemmas.census-readings
  "General lemmas: census readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-refl [x] (call 'signed/at-most-reflexive x))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn board [x k] (sel (add x (neg k)) s/zero (call 'signed/decide-at-most x k)))

(defn clamp-facts [v x k] (pconj (le s/zero v) (le (add x (neg k)) v)))

(def clamp-spec
  (let [x 'cc-x k 'cc-k D (call 'signed/decide-at-most x k) over (add x (neg k))
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['cc-e (eqb b)]] (clamp-facts (sel over s/zero b) x k)))
        kk0 (ring (add k (neg k)) s/zero)]
    (s/spec 'signed/census-clamp [['cc-x signed] ['cc-k signed]]
            (clamp-facts (board x k) x k)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['cc-b bool]] (claim 'cc-b))
                          ;; decided false: k <= x, V = x - k
                          (f/lam [['cc-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le s/zero over) (le over over)
                                          (le-resp (add k (neg k)) s/zero over over kk0 (refl over)
                                                   (call 'signed/add-right-monotone k x (neg k) (call 'signed/decide-at-most-false-reverse x k 'cc-e)))
                                          (le-refl over)))
                          ;; decided true: x <= k, V = 0
                          (f/lam [['cc-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le s/zero s/zero) (le over s/zero)
                                          (le-refl s/zero)
                                          (le-resp over over (add k (neg k)) s/zero (refl over) kk0
                                                   (call 'signed/add-right-monotone x k (neg k) (call 'signed/decide-at-most-true-sound x k 'cc-e)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn excess [N K] (f/lam [['cx-i nat]] (add (at N 'cx-i) (neg K))))

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

(def theorem-specs [clamp-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      nat-more/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-positive/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-census-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
