(ns rainbow.math.lemmas.ncd-readings
  "General lemmas: ncd readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.fulfil-readings :as ful]
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

(defn msel "the checker's min(x, y): if-at-most x y x y" [x y] (sel y x (call 'signed/decide-at-most x y)))

(defn min-facts [x y v] (pconj (le v x) (pconj (le v y) (disj (eqv v x) (eqv v y)))))

(defn stepsel "the checker's (c <= 0 ? min(M, x + 1) : 0)" [c x M] (sel s/zero (ful/msel M (add x one)) (call 'signed/decide-at-most c s/zero)))

(defn minf [M x1 v] (pconj (le v M) (pconj (le v x1) (disj (eqv v M) (eqv v x1)))))

(defn step-facts [c x M v]
  (let [x1 (add x one)]
    (pconj (disj (pconj (le c s/zero) (minf M x1 v)) (eqv v s/zero))
           (f/forall [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]] (pconj (le s/zero v) (le v M))))))

(def step-spec
  (let [c 'ns-c x 'ns-x M 'ns-M v 'ns-v x1 (add x one) w (ful/msel M x1) D (call 'signed/decide-at-most c s/zero)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['ns-de (eqb b)] ['ns-hv (eqv v (sel s/zero w b))]] (step-facts c x M v)))
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        L (pconj (le c s/zero) (minf M x1 v)) R (eqv v s/zero)
        Rng (f/forall [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]] (pconj (le s/zero v) (le v M)))]
    (s/spec 'signed/ncd-step [['ns-c signed] ['ns-x signed] ['ns-M signed] ['ns-v signed] ['ns-hv (eqv v (stepsel c x M))]]
            (step-facts c x M v)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['ns-b bool]] (claim 'ns-b))
                          ;; a claim: v ~ 0
                          (f/lam [['ns-de (eqb (f/const* 'data/false []))] ['ns-hv (eqv v s/zero)]]
                                 (conjoin (disj L R) Rng (inr L R 'ns-hv)
                                          (f/lam [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]]
                                                 (conjoin (le s/zero v) (le v M) (a/eq-le s/zero v (sym v s/zero 'ns-hv))
                                                          (le-resp s/zero v M M (sym v s/zero 'ns-hv) (refl M) 'ns-M0)))))
                          ;; clean: v ~ min(M, x + 1)
                          (f/lam [['ns-de (eqb (f/const* 'data/true []))] ['ns-hv (eqv v w)]]
                                 (let [mf (call 'signed/min-select-cases M x1)
                                       w-M (fst (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf)
                                       w-x (fst (le w x1) (disj (eqv w M) (eqv w x1)) (snd (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf))
                                       w-or (snd (le w x1) (disj (eqv w M) (eqv w x1)) (snd (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf))
                                       sv (sym v w 'ns-hv)
                                       v-M (le-resp w v M M sv (refl M) w-M)
                                       v-x (le-resp w v x1 x1 sv (refl x1) w-x)
                                       v-or (cases (eqv w M) (eqv w x1) (disj (eqv v M) (eqv v x1)) w-or
                                                   (f/lam [['ns-wm (eqv w M)]] (inl (eqv v M) (eqv v x1) (trans v w M 'ns-hv 'ns-wm)))
                                                   (f/lam [['ns-wx (eqv w x1)]] (inr (eqv v M) (eqv v x1) (trans v w x1 'ns-hv 'ns-wx))))]
                                   (conjoin (disj L R) Rng
                                            (inl L R (conjoin (le c s/zero) (minf M x1 v) (call 'signed/decide-at-most-true-sound c s/zero 'ns-de)
                                                              (conjoin (le v M) (pconj (le v x1) (disj (eqv v M) (eqv v x1))) v-M
                                                                       (conjoin (le v x1) (disj (eqv v M) (eqv v x1)) v-x v-or))))
                                            (f/lam [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]]
                                                   (let [x1-nn (le-trans s/zero x x1 'ns-x0
                                                                         (le-resp (add x s/zero) x (add x one) x1 (ring (add x s/zero) x) (refl x1)
                                                                                  (le-resp (add s/zero x) (add x s/zero) (add one x) (add x one) (ring (add s/zero x) (add x s/zero)) (ring (add one x) (add x one))
                                                                                           (call 'signed/add-right-monotone s/zero one x (f/const* 'signed/zero-at-most-one [])))))]
                                                     (conjoin (le s/zero v) (le v M)
                                                              (cases (eqv v M) (eqv v x1) (le s/zero v) v-or
                                                                     (f/lam [['ns-vm (eqv v M)]] (le-resp s/zero s/zero M v (refl s/zero) (sym v M 'ns-vm) 'ns-M0))
                                                                     (f/lam [['ns-vx (eqv v x1)]] (le-resp s/zero s/zero x1 v (refl s/zero) (sym v x1 'ns-vx) x1-nn)))
                                                              v-M))))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'ns-hv))))

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

(def theorem-specs [step-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-ncd-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
