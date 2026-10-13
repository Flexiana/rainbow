(ns rainbow.math.lemmas.wage-readings
  "General lemmas: wage readings. The mathematical facts the corresponding checks rest on,
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

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

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
           [(add x (sub y x)) (s/add-cong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn eff "the checker's max(r, W): if-at-most r W W r" [r W] (sel r W (call 'signed/decide-at-most r W)))

(defn flag "the checker's [r <= W]: if-at-most r W 1 0" [r W] (sel s/zero one (call 'signed/decide-at-most r W)))

(defn cell-facts [r W e u h p]
  (pconj (le r e) (pconj (le W e) (pconj (disj (pconj (eqv u one) (eqv e W)) (pconj (eqv u s/zero) (eqv e r)))
                                          (le (mul W h) p)))))

(def cell-spec
  (let [r 'wc-r W 'wc-W e 'wc-e u 'wc-u h 'wc-h p 'wc-p D (call 'signed/decide-at-most r W)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['wc-de (eqb b)] ['wc-he (eqv e (sel r W b))] ['wc-hu (eqv u (sel s/zero one b))]] (cell-facts r W e u h p)))
        L (pconj (eqv u one) (eqv e W)) R (pconj (eqv u s/zero) (eqv e r))
        pay (fn [w-le-e]
              (le-resp (mul W h) (mul W h) (mul e h) p (refl (mul W h)) (sym p (mul e h) 'wc-hp)
                       (call 'signed/scaled-term-at-most h W e 'wc-hh w-le-e)))
        facts (fn [r-le w-le orr]
                (conjoin (le r e) (pconj (le W e) (pconj (disj L R) (le (mul W h) p))) r-le
                         (conjoin (le W e) (pconj (disj L R) (le (mul W h) p)) w-le
                                  (conjoin (disj L R) (le (mul W h) p) orr (pay w-le)))))]
    (s/spec 'signed/wage-cell [['wc-r signed] ['wc-W signed] ['wc-e signed] ['wc-u signed] ['wc-h signed] ['wc-p signed]
                               ['wc-hh (le s/zero h)] ['wc-hp (eqv p (mul e h))]
                               ['wc-he (eqv e (eff r W))] ['wc-hu (eqv u (flag r W))]]
            (cell-facts r W e u h p)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['wc-b bool]] (claim 'wc-b))
                          ;; decided false: W <= r, e ~ r, u ~ 0
                          (f/lam [['wc-de (eqb (f/const* 'data/false []))] ['wc-he (eqv e r)] ['wc-hu (eqv u s/zero)]]
                                 (let [w-r (call 'signed/decide-at-most-false-reverse r W 'wc-de)]
                                   (facts (a/eq-le r e (sym e r 'wc-he))
                                          (le-resp W W r e (refl W) (sym e r 'wc-he) w-r)
                                          (inr L R (conjoin (eqv u s/zero) (eqv e r) 'wc-hu 'wc-he)))))
                          ;; decided true: r <= W, e ~ W, u ~ 1
                          (f/lam [['wc-de (eqb (f/const* 'data/true []))] ['wc-he (eqv e W)] ['wc-hu (eqv u one)]]
                                 (let [r-w (call 'signed/decide-at-most-true-sound r W 'wc-de)]
                                   (facts (le-resp r r W e (refl r) (sym e W 'wc-he) r-w)
                                          (a/eq-le W e (sym e W 'wc-he))
                                          (inl L R (conjoin (eqv u one) (eqv e W) 'wc-hu 'wc-he)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'wc-he 'wc-hu))))

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

(def theorem-specs [cell-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-wage-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
