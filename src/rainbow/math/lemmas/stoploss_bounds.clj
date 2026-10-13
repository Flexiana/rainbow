(ns rainbow.math.lemmas.stoploss-bounds
  "General lemmas: stoploss bounds. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.nsfr-reading :as nsfr]
            [rainbow.math.linear.matrix.affine-strong-row-contraction :as nnrat-nonneg]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.deviation-rows :as deviation]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn diff-nn [x y h]
  (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn term-facts [e k d g] (pconj (le s/zero e) (pconj (le (mul (sub k d) g) e) (le e (mul k g)))))

(def term-spec
  (let [[k d g] '[st-k st-d st-g] I (nsfr/le-ind d k) x (mul (sub k d) g) e (mul I x)
        build (fn [lo mid hi] (conjoin (le s/zero e) (pconj (le x e) (le e (mul k g))) lo (conjoin (le x e) (le e (mul k g)) mid hi)))
        ;; (k - d) g <= k g  from 0 <= d, 0 <= g:  k g - d g <= k g
        x-le-kg (le-resp (add (mul k g) (neg (mul d g))) x (add (mul k g) s/zero) (mul k g)
                         (ring (add (mul k g) (neg (mul d g))) x) (ring (add (mul k g) s/zero) (mul k g))
                         (call 'signed/add-left-monotone (neg (mul d g)) s/zero (mul k g)
                               (le-resp (neg (mul d g)) (neg (mul d g)) (neg s/zero) s/zero (refl (neg (mul d g))) (ring (neg s/zero) s/zero)
                                        (call 'signed/negate-reverses-order s/zero (mul d g) (nonneg-prod d g 'st-hd 'st-hg)))))
        kg-nn (nonneg-prod k g 'st-hk 'st-hg)]
    (s/spec 'signed/stoploss-term-bracket
            [['st-k signed] ['st-d signed] ['st-g signed] ['st-hk (le s/zero k)] ['st-hd (le s/zero d)] ['st-hg (le s/zero g)]]
            (term-facts e k d g)
            (cases (pconj (le d k) (eqv I one)) (pconj (lt k d) (eqv I s/zero)) (term-facts e k d g)
                   (call 'signed/le-indicator-reading d k)
                   ;; I ~ 1, d <= k: e ~ x
                   (f/lam [['st-a (pconj (le d k) (eqv I one))]]
                          (let [i1 (pright (le d k) (eqv I one) 'st-a)
                                ex (a/chain e [(mul one x) (mcong I one x x i1 (refl x))] [x (call 'signed/multiply-one-left x)])
                                x-nn (nonneg-prod (sub k d) g (diff-nn d k (pleft (le d k) (eqv I one) 'st-a)) 'st-hg)
                                xe (sym e x ex)]
                            (build (le-resp s/zero s/zero x e (refl s/zero) xe x-nn)
                                   (a/eq-le x e xe)
                                   (le-resp x e (mul k g) (mul k g) xe (refl (mul k g)) x-le-kg))))
                   ;; I ~ 0, k < d: e ~ 0, x <= 0
                   (f/lam [['st-b (pconj (lt k d) (eqv I s/zero))]]
                          (let [i0 (pright (lt k d) (eqv I s/zero) 'st-b)
                                e0 (a/chain e [(mul s/zero x) (mcong I s/zero x x i0 (refl x))] [s/zero (call 'signed/multiply-zero-left x)])
                                kd (call 'signed/less-than-implies-at-most k d (pleft (lt k d) (eqv I s/zero) 'st-b))
                                ;; k - d <= 0, so (k - d) g <= 0 g ~ 0
                                kd-np (le-resp (sub k d) (sub k d) (sub d d) s/zero (refl (sub k d)) (ring (sub d d) s/zero)
                                               (call 'signed/add-right-monotone k d (neg d) kd))
                                x-np (le-resp (mul (sub k d) g) x (mul s/zero g) s/zero (refl x) (call 'signed/multiply-zero-left g)
                                              (call 'signed/multiply-right-monotone g (sub k d) s/zero 'st-hg kd-np))
                                ze (sym e s/zero e0)]
                            (build (a/eq-le s/zero e ze)
                                   (le-resp x x s/zero e (refl x) ze x-np)
                                   (le-resp s/zero e (mul k g) (mul k g) ze (refl (mul k g)) kg-nn))))))))

(defn fam [h] (f/lam [['sf-k nat]] (h 'sf-k)))

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

(def theorem-specs [term-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      nnrat-nonneg/extend-environment
      deviation/extend-environment
      (support/extend-with-shared :expr-sum-stoploss-bounds theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
