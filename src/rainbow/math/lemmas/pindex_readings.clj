(ns rainbow.math.lemmas.pindex-readings
  "General lemmas: pindex readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.square-monotone :as square-monotone]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn sq [x] (mul x x))

(def square-reflects-spec
  (let [x 'sr-a y 'sr-b goal (le x y)]
    (s/spec 'signed/square-reflects-order [['sr-a signed] ['sr-b signed] ['sr-hb (le s/zero y)] ['sr-h (le (sq x) (sq y))]]
            goal
            (cases (le x y) (le y x) goal (call 'signed/at-most-total x y)
                   (f/lam [['sr-xy (le x y)]] 'sr-xy)
                   (f/lam [['sr-yx (le y x)]]
                          (let [hx (le-trans s/zero y x 'sr-hb 'sr-yx)
                                same (anti (sq x) (sq y) 'sr-h (call 'signed/square-monotone y x 'sr-hb 'sr-yx))
                                prod (a/chain (mul (sub x y) (add x y))
                                              [(sub (sq x) (sq y)) (ring (mul (sub x y) (add x y)) (sub (sq x) (sq y)))]
                                              [(sub (sq y) (sq y)) (s/add-cong (sq x) (sq y) (neg (sq y)) (neg (sq y)) same (refl (neg (sq y))))]
                                              [s/zero (ring (sub (sq y) (sq y)) s/zero)])]
                            (cases (eqv (sub x y) s/zero) (eqv (add x y) s/zero) goal (call 'signed/multiply-zero-split (sub x y) (add x y) prod)
                                   (f/lam [['sr-d (eqv (sub x y) s/zero)]]
                                          (a/eq-le x y (a/chain x [(add (sub x y) y) (ring x (add (sub x y) y))]
                                                                [(add s/zero y) (s/add-cong (sub x y) s/zero y y 'sr-d (refl y))]
                                                                [y (ring (add s/zero y) y)])))
                                   ;; x + y ~ 0 with 0 <= x, 0 <= y: x <= x + y ~ 0 <= y
                                   (f/lam [['sr-s (eqv (add x y) s/zero)]]
                                          (le-trans x s/zero y
                                                    (le-resp (add x s/zero) x (add x y) s/zero (call 'signed/add-zero-right x) 'sr-s
                                                             (call 'signed/add-left-monotone s/zero y x 'sr-hb))
                                                    'sr-hb)))))))))

(defn pinned [x d v] (f/forall [['pn-x signed] ['pn-h (eqv (mul 'pn-x d) v)]] (eqv 'pn-x x)))

(defn bracket [L P F Fu]
  (f/forall [['rt-r signed] ['rt-nn (le s/zero 'rt-r)] ['rt-sq (eqv (sq 'rt-r) (mul L P))]]
            (pconj (le F 'rt-r) (f/arrow (le s/zero Fu) (le 'rt-r Fu)))))

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

(def borrowed-specs [hhi/positive-spec])

(def theorem-specs [square-reflects-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      square-monotone/extend-environment
      (support/extend-with-shared :expr-sum-pindex-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
