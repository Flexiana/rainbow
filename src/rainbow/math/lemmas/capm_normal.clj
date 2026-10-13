(ns rainbow.math.lemmas.capm-normal
  "General lemmas: capm normal. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(def mean-residual-spec
  (let [[N rm al be mm] '[mr-n mr-rm mr-al mr-be mr-mm]
        lhs (sub (mul N rm) (add (mul al N) (mul be (mul N mm))))]
    (s/spec 'signed/capm-mean-residual
            [['mr-n signed] ['mr-rm signed] ['mr-al signed] ['mr-be signed] ['mr-mm signed] ['mr-h (eqv (add al (mul be mm)) rm)]]
            (eqv lhs s/zero)
            (a/chain lhs
                     [(mul N (sub rm (add al (mul be mm)))) (ring lhs (mul N (sub rm (add al (mul be mm)))))]
                     [(mul N (sub rm rm)) (mcong N N (sub rm (add al (mul be mm))) (sub rm rm) (refl N)
                                                 (acong rm rm (neg (add al (mul be mm))) (neg rm) (refl rm) (a/neg-cong (add al (mul be mm)) rm 'mr-h)))]
                     [s/zero (ring (mul N (sub rm rm)) s/zero)]))))

(def residual-term-spec
  (let [[r rm al be m mm] '[rt-r rt-rm rt-al rt-be rt-m rt-mm]
        d (sub m mm) q (sub r rm) al' (sub rm (mul be mm))
        lhs (mul (sub r (add al (mul be m))) d)
        rhs (sub (mul d q) (mul be (mul d d)))]
    (s/spec 'signed/capm-residual-term
            [['rt-r signed] ['rt-rm signed] ['rt-al signed] ['rt-be signed] ['rt-m signed] ['rt-mm signed] ['rt-h (eqv al al')]]
            (eqv lhs rhs)
            (a/chain lhs
                     [(mul (sub r (add al' (mul be m))) d)
                      (mcong (sub r (add al (mul be m))) (sub r (add al' (mul be m))) d d
                             (acong r r (neg (add al (mul be m))) (neg (add al' (mul be m))) (refl r)
                                    (a/neg-cong (add al (mul be m)) (add al' (mul be m)) (acong al al' (mul be m) (mul be m) 'rt-h (refl (mul be m)))))
                             (refl d))]
                     [rhs (ring (mul (sub r (add al' (mul be m))) d) rhs)]))))

(defn fam [g] (f/lam [['cf-t nat]] (g 'cf-t)))

(defn residual [m r alpha beta] (fam #(sub (at r %) (add alpha (mul beta (at m %))))))

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

(def theorem-specs [mean-residual-spec residual-term-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      of-nat/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-capm-normal theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
