(ns rainbow.math.lemmas.fgt-order
  "General lemmas: fgt order. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.deviation-rows :as deviation]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

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

(defn bool-cases [motive D false-case true-case]
  (f/app (f/app (f/const* 'data/Bool.rec [prop-level]) motive false-case true-case D)
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(defn clamp [v] (sel s/zero v (call 'signed/decide-at-most s/zero v)))

(defn clamp-facts [v w]
  (pconj (le s/zero (clamp v))
         (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le (clamp v) w)))
                (f/arrow (le v s/zero) (eqv (clamp v) s/zero)))))

(def clamp-spec
  (let [v 'fc-v w 'fc-w D (call 'signed/decide-at-most s/zero v)
        eqb (fn [b] (f/equality type-level bool D b))
        facts (fn [c] (pconj (le s/zero c) (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)))))
        build (fn [c nn bound zero]
                (conjoin (le s/zero c) (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)))
                         nn (conjoin (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)) bound zero)))]
    (s/spec 'signed/fgt-clamp-bounds [['fc-v signed] ['fc-w signed]]
            (clamp-facts v w)
            (bool-cases (f/lam [['fc-b bool]] (f/forall [['fc-e (eqb 'fc-b)]] (facts (sel s/zero v 'fc-b)))) D
                        ;; decided false: g = 0
                        (f/lam [['fc-e (eqb bfalse)]]
                               (build s/zero (le-refl s/zero)
                                      (f/lam [['fc-a (le v w)] ['fc-z (le s/zero w)]] 'fc-z)
                                      (f/lam [['fc-n (le v s/zero)]] (refl s/zero))))
                        ;; decided true: 0 <= v, g = v
                        (f/lam [['fc-e (eqb btrue)]]
                               (let [pos (call 'signed/decide-at-most-true-sound s/zero v 'fc-e)]
                                 (build v pos
                                        (f/lam [['fc-a (le v w)] ['fc-z (le s/zero w)]] 'fc-a)
                                        (f/lam [['fc-n (le v s/zero)]] (anti v s/zero 'fc-n pos)))))))))

(defn indicator [y z] (sel one s/zero (call 'signed/decide-at-most z y)))

(def gap-indicator-spec
  (let [[g y z] '[gi-g gi-y gi-z] D (call 'signed/decide-at-most z y) v (sub z y)
        eqb (fn [b] (f/equality type-level bool D b))
        goal (fn [b] (le g (mul z (sel one s/zero b))))
        cf (call 'signed/fgt-clamp-bounds v z)
        cnn (pleft (le s/zero (clamp v)) (pconj (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero))) cf)
        rest (pright (le s/zero (clamp v)) (pconj (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero))) cf)
        cbound (pleft (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero)) rest)
        czero (pright (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero)) rest)
        ;; z - y <= z - 0 ~ z  (0 <= y)
        v-le-z (le-resp v v (sub z s/zero) z (refl v) (ring (sub z s/zero) z)
                        (call 'signed/add-left-monotone (neg y) (neg s/zero) z (call 'signed/negate-reverses-order s/zero y 'gi-hy)))]
    (s/spec 'signed/fgt-gap-indicator
            [['gi-g signed] ['gi-y signed] ['gi-z signed] ['gi-hg (eqv g (clamp v))] ['gi-hy (le s/zero y)] ['gi-hz (le s/zero z)]]
            (goal D)
            (bool-cases (f/lam [['gi-b bool]] (f/forall [['gi-e (eqb 'gi-b)]] (goal 'gi-b))) D
                        ;; decided false (not z <= y): indicator 1, g <= z ~ z 1
                        (f/lam [['gi-e (eqb bfalse)]]
                               (le-resp g g z (mul z one) (refl g) (sym (mul z one) z (trans (mul z one) (mul one z) z (call 'signed/multiply-commutative z one) (call 'signed/multiply-one-left z)))
                                        (le-resp (clamp v) g z z (sym g (clamp v) 'gi-hg) (refl z) (f/app (f/app cbound v-le-z) 'gi-hz))))
                        ;; decided true (z <= y): z - y <= 0, g ~ clamp ~ 0 ~ z 0
                        (f/lam [['gi-e (eqb btrue)]]
                               (let [zy (call 'signed/decide-at-most-true-sound z y 'gi-e)
                                     v-nonpos (le-resp v v (sub y y) s/zero (refl v) (ring (sub y y) s/zero)
                                                       (call 'signed/add-right-monotone z y (neg y) zy))
                                     g0 (trans g (clamp v) s/zero 'gi-hg (f/app czero v-nonpos))]
                                 (a/eq-le g (mul z s/zero) (trans g s/zero (mul z s/zero) g0 (sym (mul z s/zero) s/zero (call 'signed/multiply-zero-right z))))))))))

(defn fam [g] (f/lam [['ff-t nat]] (g 'ff-t)))

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

(def theorem-specs [clamp-spec gap-indicator-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-positive/extend-environment
      multiply-ring/extend-environment
      deviation/extend-environment
      (support/extend-with-shared :expr-sum-fgt-order theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
