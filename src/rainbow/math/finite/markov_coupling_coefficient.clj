(ns rainbow.math.finite.markov-coupling-coefficient
  "Charge off-diagonal residual coupling costs to the Dobrushin coefficient.
  Positive residual mass is explicit here; the zero branch is separate."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-coupling-distance :as distance]
            [rainbow.math.finite.markov-residual-coupling :as residual]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.rational.signed.geometric-bridge :as embedding]
            [rainbow.math.rational.nnrat.map-sum-on :as sums-on]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat residual/nnrat)
(def one (c 'nnrat/one))
(def half (c 'nnrat/half))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(def two (add one one))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- items [] (poly 'finset-data/enumeration 'S 'states))
(defn- member [x] (poly 'list/membership 'S (items) x))
(defn- sum [mapping] (poly 'nnrat/map-sum 'S mapping (items)))
(defn- same-sum [a b pointwise]
  (poly 'nnrat/map-sum-respects-equivalence 'S a b pointwise (items)))
(defn- monotone-sum [a b bound]
  (poly 'nnrat/map-sum-monotone-on 'S a b (items) bound))
(defn- total [mapping] (poly 'probability/nnrat-total-mass 'S 'states mapping))
(defn- l1 [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
(defn- step [mass] (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
(defn- delta [] (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel))
(def coefficient-binders
  [['rho nnrat]
   ['coefficient-bound (app 'signed/at-most (delta) (app 'signed/from-nnrat 'rho))]])

(defn- unhalf [d]
  (let [a (mul two (mul half d)) b (mul (mul half two) d) end (mul one d)]
    (trans a b d (ring/equiv a b)
      (trans b end d
        (app 'nnrat/multiply-respects-equivalence (mul half two) one d d
             (c 'nnrat/half-times-two-equivalent-one) (refl d))
        (app 'nnrat/multiply-one-left d)))))

(def row-l1-at-most-twice-rho-spec
  (let [bindings (into (into coefficient/base-binders coefficient-binders)
                       [['i 'S] ['i-member (member 'i)] ['j 'S] ['j-member (member 'j)]])
        d (l1 (f/app 'kernel 'i) (f/app 'kernel 'j)) h (mul half d)
        bounded
        (app 'signed/from-nnrat-at-most-reverse h 'rho
          (app 'signed/at-most-transitive (app 'signed/from-nnrat h) (delta)
               (app 'signed/from-nnrat 'rho)
               (poly 'markov/row-distance-at-most-dobrushin-coefficient
                     'S 'states 'kernel 'i 'i-member 'j 'j-member)
               'coefficient-bound))]
    {:name 'markov/nnrat-row-l1-at-most-twice-dobrushin-bound :universes ['u]
     :type (f/forall bindings (le d (mul two 'rho)))
     :value (f/lam bindings
              (app 'nnrat/at-most-respects-equivalence d (mul two h)
                   (mul two 'rho) (mul two 'rho)
                   (sym (mul two h) d (unhalf d)) (refl (mul two 'rho))
                   (app 'nnrat/multiply-monotone two h 'rho bounded)))}))

(defn- joint-total []
  (sum (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (f/app 'joint 'i 'j))))))
(defn- joint-cost []
  (sum (f/lam [['i 'S]]
    (sum (f/lam [['j 'S]]
      (mul (f/app 'joint 'i 'j) (l1 (f/app 'kernel 'i) (f/app 'kernel 'j))))))))

(def coupling-cost-at-most-spec
  (let [bindings (conj (into coefficient/base-binders coefficient-binders)
                       ['joint (f/arrow 'S 'S nnrat)])
        r (mul two 'rho)
        cost-row (f/lam [['i 'S]]
                   (sum (f/lam [['j 'S]]
                     (mul (f/app 'joint 'i 'j) (l1 (f/app 'kernel 'i) (f/app 'kernel 'j))))))
        scaled-row (f/lam [['i 'S]]
                     (sum (f/lam [['j 'S]] (mul (f/app 'joint 'i 'j) r))))
        row-mass (f/lam [['i 'S]] (sum (f/lam [['j 'S]] (f/app 'joint 'i 'j))))
        factored (f/lam [['i 'S]] (mul (f/app row-mass 'i) r))
        factor-proof
        (trans (sum scaled-row) (sum factored) (mul (joint-total) r)
          (same-sum scaled-row factored
            (f/lam [['i 'S]]
              (sym (f/app factored 'i) (f/app scaled-row 'i)
                (poly 'nnrat/map-sum-scale-right 'S
                      (f/lam [['j 'S]] (f/app 'joint 'i 'j)) r (items)))))
          (sym (mul (joint-total) r) (sum factored)
               (poly 'nnrat/map-sum-scale-right 'S row-mass r (items))))]
    {:name 'markov/nnrat-coupling-row-cost-at-most-dobrushin-bound :universes ['u]
     :type (f/forall bindings (le (joint-cost) (mul (joint-total) r)))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-respects-equivalence
         (joint-cost) (joint-cost) (mul (joint-total) r) (sum scaled-row)
         (refl (joint-cost)) (sym (sum scaled-row) (mul (joint-total) r) factor-proof)
         (monotone-sum cost-row scaled-row
           (f/lam [['i 'S] ['i-member (member 'i)]]
             (monotone-sum
               (f/lam [['j 'S]] (mul (f/app 'joint 'i 'j)
                                    (l1 (f/app 'kernel 'i) (f/app 'kernel 'j))))
               (f/lam [['j 'S]] (mul (f/app 'joint 'i 'j) r))
               (f/lam [['j 'S] ['j-member (member 'j)]]
                 (app 'nnrat/multiply-monotone (f/app 'joint 'i 'j)
                   (l1 (f/app 'kernel 'i) (f/app 'kernel 'j)) r
                   (poly 'markov/nnrat-row-l1-at-most-twice-dobrushin-bound
                         'S 'states 'kernel 'rho 'coefficient-bound 'i 'i-member 'j 'j-member))))))))}))

(defn- positive-mass [] (app 'nnrat/make (app 'data/succ 'ap) 'adp))
(defn- twice [a]
  (trans (mul two a) (add (mul one a) (mul one a)) (add a a)
    (app 'nnrat/multiply-distributes-add-right one one a)
    (app 'nnrat/add-respects-equivalence (mul one a) a (mul one a) a
         (app 'nnrat/multiply-one-left a) (app 'nnrat/multiply-one-left a))))
(defn- input-l1-twice-residual []
  (let [p (total (residual/residual-mapping :left)) q (total (residual/residual-mapping :right))
        m (positive-mass)
        q-m (trans q p m
              (sym p q (poly 'markov/nnrat-residual-totals-equal 'S 'states 'left 'right 'same-total))
              'positive-residual-total)]
    (trans (l1 'left 'right) (add p q) (mul two m)
      (poly 'markov/nnrat-total-variation-is-residual-total-sum 'S 'states 'left 'right)
      (trans (add p q) (add m m) (mul two m)
        (app 'nnrat/add-respects-equivalence p m q m 'positive-residual-total q-m)
        (sym (mul two m) (add m m) (twice m))))))

(def positive-residual-contraction-spec
  (let [bindings (into distance/positive-residual-binders coefficient-binders)
        j (poly 'markov/nnrat-product-coupling 'S 'states
                (residual/residual-mapping :left) (residual/residual-mapping :right) (positive-mass))
        cost (f/app (f/lam [['joint (f/arrow 'S 'S nnrat)]] (joint-cost)) j)
        mass (f/app (f/lam [['joint (f/arrow 'S 'S nnrat)]] (joint-total)) j)
        args ['S 'states 'left 'right 'kernel 'ap 'adp 'same-total 'positive-residual-total]
        lhs (l1 (step 'left) (step 'right)) rhs (mul 'rho (l1 'left 'right))
        r (mul two 'rho) mr (mul mass r) m (positive-mass)
        factor
        (trans mr (mul m r) rhs
          (app 'nnrat/multiply-respects-equivalence mass m r r
               (apply poly 'markov/nnrat-positive-residual-coupling-total args) (refl r))
          (trans (mul m r) (mul 'rho (mul two m)) rhs
            (ring/equiv (mul m r) (mul 'rho (mul two m)))
            (app 'nnrat/multiply-respects-equivalence 'rho 'rho (mul two m) (l1 'left 'right)
                 (refl 'rho) (sym (l1 'left 'right) (mul two m) (input-l1-twice-residual)))))]
    {:name 'markov/nnrat-kernel-step-positive-residual-contraction :universes ['u]
     :type (f/forall bindings (le lhs rhs))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-transitive lhs cost rhs
         (apply poly 'markov/nnrat-kernel-step-positive-residual-coupling-bound args)
         (app 'nnrat/at-most-respects-equivalence cost cost rhs mr
           (refl cost) (sym mr rhs factor)
           (poly 'markov/nnrat-coupling-row-cost-at-most-dobrushin-bound
                 'S 'states 'kernel 'rho 'coefficient-bound j))))}))

(def theorem-specs [row-l1-at-most-twice-rho-spec coupling-cost-at-most-spec
                    positive-residual-contraction-spec])
(defn extend-environment [env]
  (-> env distance/extend-environment coefficient/extend-environment sums-on/extend-environment
      ((fn [e] (if (environment/resolve-id e 'signed/from-nnrat-at-most-reverse) e
                 (support/add-spec e :finite-markov-coupling-coefficient-support
                                   embedding/from-nnrat-at-most-reverse-spec))))
      (support/extend-with :finite-markov-coupling-coefficient theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
