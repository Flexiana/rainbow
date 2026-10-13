(ns rainbow.math.lemmas.projgrad-clamp
  "General lemmas: projgrad clamp. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

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

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn sides [y p z] [(pconj (le y p) (le p z)) (pconj (le p y) (le z p))])

(def projection-sign-spec
  (let [[y p z] '[cp-y cp-p cp-z] [L R] (sides y p z) u (sub y p) v (sub z p) goal (le (mul u v) s/zero)
        ;; a <= b  ->  a - p <= b - p
        shift (fn [a b h] (call 'signed/add-right-monotone a b (neg p) h))
        pp (ring (sub p p) s/zero)]
    (s/spec 'signed/clamp-projection-sign
            [['cp-y signed] ['cp-p signed] ['cp-z signed] ['cp-h (disj L R)]]
            goal
            (cases L R goal 'cp-h
                   (f/lam [['cp-l L]]
                          (let [u-np (le-resp u u (sub p p) s/zero (refl u) pp (shift y p (pleft (le y p) (le p z) 'cp-l)))
                                v-nn (le-resp (sub p p) s/zero v v pp (refl v) (shift p z (pright (le y p) (le p z) 'cp-l)))]
                            (le-resp (mul u v) (mul u v) (mul s/zero v) s/zero (refl (mul u v)) (ring (mul s/zero v) s/zero)
                                     (call 'signed/multiply-right-monotone v u s/zero v-nn u-np))))
                   (f/lam [['cp-r R]]
                          (let [u-nn (le-resp (sub p p) s/zero u u pp (refl u) (shift p y (pleft (le p y) (le z p) 'cp-r)))
                                v-np (le-resp v v (sub p p) s/zero (refl v) pp (shift z p (pright (le p y) (le z p) 'cp-r)))]
                            (le-resp (mul u v) (mul u v) (mul u s/zero) s/zero (refl (mul u v)) (ring (mul u s/zero) s/zero)
                                     (call 'signed/multiply-left-monotone u v s/zero u-nn v-np))))))))

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

(def theorem-specs [projection-sign-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-projgrad-clamp theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
