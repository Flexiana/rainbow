(ns rainbow.math.lemmas.frankw-corner
  "General lemmas: frankw corner. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.deviation-rows :as deviation]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(def coordinate-min-spec
  (let [[g sv lo hi y] '[fc-g fc-s fc-lo fc-hi fc-y] goal (le (mul g sv) (mul g y))]
    (s/spec 'signed/frankw-coordinate-min
            [['fc-g signed] ['fc-s signed] ['fc-lo signed] ['fc-hi signed] ['fc-y signed]
             ['fc-sl (le (mul g sv) (mul g lo))] ['fc-sh (le (mul g sv) (mul g hi))] ['fc-ly (le lo y)] ['fc-yh (le y hi)]]
            goal
            (cases (le s/zero g) (le g s/zero) goal (call 'signed/at-most-total s/zero g)
                   (f/lam [['fc-p (le s/zero g)]]
                          (le-trans (mul g sv) (mul g lo) (mul g y) 'fc-sl (call 'signed/multiply-left-monotone g lo y 'fc-p 'fc-ly)))
                   (f/lam [['fc-n (le g s/zero)]]
                          (let [ng-nn (le-resp (neg s/zero) s/zero (neg g) (neg g) (ring (neg s/zero) s/zero) (refl (neg g))
                                               (call 'signed/negate-reverses-order g s/zero 'fc-n))
                                ;; (-g) y <= (-g) hi, negated: g hi <= g y
                                hy (le-resp (neg (mul (neg g) hi)) (mul g hi) (neg (mul (neg g) y)) (mul g y)
                                            (ring (neg (mul (neg g) hi)) (mul g hi)) (ring (neg (mul (neg g) y)) (mul g y))
                                            (call 'signed/negate-reverses-order (mul (neg g) y) (mul (neg g) hi)
                                                  (call 'signed/multiply-left-monotone (neg g) y hi ng-nn 'fc-yh)))]
                            (le-trans (mul g sv) (mul g hi) (mul g y) 'fc-sh hy)))))))

(defn fam [h] (f/lam [['ff-t nat]] (h 'ff-t)))

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

(def theorem-specs [coordinate-min-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      deviation/extend-environment
      (support/extend-with-shared :expr-sum-frankw-corner theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
