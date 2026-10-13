(ns rainbow.math.lemmas.nsfr-reading
  "General lemmas: nsfr reading. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn lt [x y] (call 'signed/less-than x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn le-ind [l r] (sel s/zero one (call 'signed/decide-at-most l r)))

(defn reading [l r v] (disj (pconj (le l r) (eqv v one)) (pconj (lt r l) (eqv v s/zero))))

(def reading-spec
  (let [l 'lr-l r 'lr-r D (call 'signed/decide-at-most l r)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['lr-e (eqb b)]] (reading l r (sel s/zero one b))))]
    (s/spec 'signed/le-indicator-reading [['lr-l signed] ['lr-r signed]]
            (reading l r (le-ind l r))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['lr-b bool]] (claim 'lr-b))
                          ;; decided false: r < l, value 0
                          (f/lam [['lr-e (eqb (f/const* 'data/false []))]]
                                 (let [rl (call 'signed/decide-at-most-false-reverse l r 'lr-e)
                                       strict (call 'signed/less-than-intro r l rl
                                                    (f/lam [['lr-q (eqv r l)]]
                                                           (f/app (call 'signed/decide-at-most-false-sound l r 'lr-e)
                                                                  (a/eq-le l r (sym r l 'lr-q)))))]
                                   (inr (pconj (le l r) (eqv s/zero one)) (pconj (lt r l) (eqv s/zero s/zero))
                                        (conjoin (lt r l) (eqv s/zero s/zero) strict (refl s/zero)))))
                          ;; decided true: l <= r, value 1
                          (f/lam [['lr-e (eqb (f/const* 'data/true []))]]
                                 (inl (pconj (le l r) (eqv one one)) (pconj (lt r l) (eqv one s/zero))
                                      (conjoin (le l r) (eqv one one) (call 'signed/decide-at-most-true-sound l r 'lr-e) (refl one))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn weighted [w x] (f/lam [['nw-i nat]] (mul (at w 'nw-i) (at x 'nw-i))))

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

(def theorem-specs [reading-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-nsfr-reading theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
