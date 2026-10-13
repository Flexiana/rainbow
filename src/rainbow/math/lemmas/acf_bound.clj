(ns rainbow.math.lemmas.acf-bound
  "General lemmas: acf bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.value-append :as append]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.linear.vector.norm-nonnegative :as square-nn]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn nadd [x y] (call 'algebra/nat-add x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn sq [x] (mul x x))

(defn dbl [x] (add x x))

(defn sqnn [x] (call 'signed/zero-at-most-of-nonnegative (mul x x) (call 'signed/square-nonnegative x)))

(defn le-add [x y hy] (le-resp (add x s/zero) x (add x y) (add x y) (ring (add x s/zero) x) (refl (add x y)) (call 'signed/add-left-monotone s/zero y x hy)))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(def term-up-spec
  (let [[x y] '[at-a at-b] lhs (dbl (mul x y)) rhs (add (sq x) (sq y))]
    (s/spec 'signed/acf-pair-upper [['at-a signed] ['at-b signed]]
            (le lhs rhs)
            (le-resp lhs lhs (add lhs (sq (sub x y))) rhs (refl lhs) (ring (add lhs (sq (sub x y))) rhs) (le-add lhs (sq (sub x y)) (sqnn (sub x y)))))))

(def term-lo-spec
  (let [[x y] '[al-a al-b] v (add (dbl (mul x y)) (add (sq x) (sq y)))]
    (s/spec 'signed/acf-pair-lower [['al-a signed] ['al-b signed]]
            (le s/zero v)
            (le-resp s/zero s/zero (sq (add x y)) v (refl s/zero) (ring (sq (add x y)) v) (sqnn (add x y))))))

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

(def theorem-specs [term-up-spec term-lo-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      append/extend-environment
      nat-infinite/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      square-nn/extend-environment
      (support/extend-with-shared :expr-sum-acf-bound theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
