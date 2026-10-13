(ns rainbow.math.finite.markov-residual-expansion
  "Canonical common mass cancels after a kernel step.

  For c=min(left,right), p=left residual and q=right residual:
    step(left) ~ step(p)+step(c), step(right) ~ step(q)+step(c);
    L1(step(left),step(right)) ~ L1(step(p),step(q)).
  Opening the residual sums gives a double-sum distance upper bound. These
  laws hold for every finite nonnegative kernel; normalization and equal
  total mass are not needed. The all-pairs Dobrushin estimate is a later step."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.shared-residual-mass :as residual]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.finite.markov-total-variation-translation :as translation]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (c 'nnrat/NonnegativeRational))
(def bindings
  [['S type-u] ['states (poly 'finset-data/Finset 'S)]
   ['kernel (f/arrow 'S 'S nnrat)]
   ['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]])
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- dist [a b] (app 'nnrat/distance a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- items [] (poly 'finset-data/enumeration 'S 'states))
(defn- sum [mapping] (poly 'nnrat/map-sum 'S mapping (items)))
(defn- common []
  (f/lam [['i 'S]] (app 'minmax/min (f/app 'left 'i) (f/app 'right 'i))))
(defn- remainder [side]
  (f/lam [['i 'S]]
    (app (if (= side :left) 'nnrat/left-residual-mass 'nnrat/right-residual-mass)
         (f/app 'left 'i) (f/app 'right 'i))))
(defn- step [mass] (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
(defn- l1 [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
(defn- flow [mass target]
  (f/lam [['i 'S]] (mul (f/app mass 'i) (f/app 'kernel 'i target))))
(defn- split-step [side target]
  (add (f/app (step (remainder side)) target) (f/app (step (common)) target)))

(defn- reconstruction [side]
  (let [mass (if (= side :left) 'left 'right)
        r (remainder side) common-mass (common)
        lhs (f/app (step mass) 'target)
        rf (flow r 'target) cf (flow common-mass 'target)
        expanded (f/lam [['i 'S]] (add (f/app rf 'i) (f/app cf 'i)))
        mi (f/app mass 'i) pi (f/app r 'i) ci (f/app common-mass 'i)
        ki (f/app 'kernel 'i 'target)
        shared-proof (app (if (= side :left)
                           'nnrat/shared-plus-left-residual
                           'nnrat/shared-plus-right-residual)
                          (f/app 'left 'i) (f/app 'right 'i))
        pointwise
        (f/lam [['i 'S]]
          (trans (mul mi ki) (mul (add ci pi) ki) (add (mul pi ki) (mul ci ki))
                 (app 'nnrat/multiply-respects-equivalence
                      mi (add ci pi) ki ki (sym (add ci pi) mi shared-proof) (refl ki))
                 (ring/equiv (mul (add ci pi) ki) (add (mul pi ki) (mul ci ki)))))]
    (trans lhs (sum expanded) (split-step side 'target)
           (poly 'nnrat/map-sum-respects-equivalence
                 'S (flow mass 'target) expanded pointwise (items))
           (poly 'nnrat/map-sum-add 'S rf cf (items)))))

(defn- reconstruction-spec [side name]
  (let [mass (if (= side :left) 'left 'right)
        bs (conj bindings ['target 'S])]
    {:name name :universes ['u]
     :type (f/forall bs (eqv (f/app (step mass) 'target) (split-step side 'target)))
     :value (f/lam bs (reconstruction side))}))

(def left-decomposition-spec
  (reconstruction-spec :left 'markov/nnrat-kernel-step-left-residual-decomposition))
(def right-decomposition-spec
  (reconstruction-spec :right 'markov/nnrat-kernel-step-right-residual-decomposition))

(def residual-cancellation-spec
  (let [p (step (remainder :left)) q (step (remainder :right))
        shifted-p (f/lam [['target 'S]] (split-step :left 'target))
        shifted-q (f/lam [['target 'S]] (split-step :right 'target))
        lhs (l1 (step 'left) (step 'right))]
    {:name 'markov/nnrat-kernel-step-total-variation-residual :universes ['u]
     :type (f/forall bindings (eqv lhs (l1 p q)))
     :value
     (f/lam bindings
       (trans lhs (l1 shifted-p shifted-q) (l1 p q)
              (poly 'markov/nnrat-total-variation-respects-pointwise-equivalent
                    'S 'states (step 'left) shifted-p (step 'right) shifted-q
                    (f/lam [['target 'S]]
                      (poly 'markov/nnrat-kernel-step-left-residual-decomposition
                            'S 'states 'kernel 'left 'right 'target))
                    (f/lam [['target 'S]]
                      (poly 'markov/nnrat-kernel-step-right-residual-decomposition
                            'S 'states 'kernel 'left 'right 'target)))
              (poly 'markov/nnrat-total-variation-common-mass
                    'S 'states p q (step (common)))))}))

(defn- residual-distance-sum [target]
  (sum (f/lam [['i 'S]]
         (dist (f/app (flow (remainder :left) target) 'i)
               (f/app (flow (remainder :right) target) 'i)))))

(def residual-expansion-bound-spec
  (let [p (step (remainder :left)) q (step (remainder :right))
        lhs (l1 (step 'left) (step 'right))
        upper-map (f/lam [['target 'S]] (residual-distance-sum 'target))
        residual-distances (f/lam [['target 'S]] (dist (f/app p 'target) (f/app q 'target)))
        upper (sum upper-map)]
    {:name 'markov/nnrat-kernel-step-residual-expansion-bound :universes ['u]
     :type (f/forall bindings (le lhs upper))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-respects-equivalence
            lhs (l1 p q) upper upper
            (poly 'markov/nnrat-kernel-step-total-variation-residual
                  'S 'states 'kernel 'left 'right)
            (refl upper)
            (poly 'nnrat/map-sum-monotone 'S residual-distances upper-map
                  (f/lam [['target 'S]]
                    (poly 'nnrat/map-sum-distance-bound 'S
                          (flow (remainder :left) 'target)
                          (flow (remainder :right) 'target) (items)))
                  (items))))}))

(defn- residual-weight [i]
  (add (f/app (remainder :left) i) (f/app (remainder :right) i)))

(defn- scaled-residual-bound [i target]
  (let [p (f/app (remainder :left) i) q (f/app (remainder :right) i)
        k (f/app 'kernel i target)
        lhs (dist (mul p k) (mul q k))
        swapped (dist (mul k p) (mul k q))
        radius (dist p q)
        original-radius (dist (f/app 'left i) (f/app 'right i))
        weight (residual-weight i)
        radius-eq-weight
        (trans radius original-radius weight
               (app 'nnrat/residual-masses-preserve-distance (f/app 'left i) (f/app 'right i))
               (app 'nnrat/distance-is-residual-mass-sum (f/app 'left i) (f/app 'right i)))]
    (app 'nnrat/at-most-respects-equivalence
         lhs swapped (mul k weight) (mul k radius)
         (app 'nnrat/distance-respects-equivalence
              (mul p k) (mul k p) (mul q k) (mul k q)
              (app 'nnrat/multiply-commutative p k)
              (app 'nnrat/multiply-commutative q k))
         (app 'nnrat/multiply-respects-equivalence
              k k weight radius (refl k) (sym radius weight radius-eq-weight))
         (app 'nnrat/distance-multiply-left-bound k p q))))

(def residual-weighted-expansion-bound-spec
  (let [lhs (l1 (step 'left) (step 'right))
        raw (f/lam [['target 'S]] (residual-distance-sum 'target))
        weighted-inner (fn [target]
                         (f/lam [['i 'S]]
                           (mul (f/app 'kernel 'i target) (residual-weight 'i))))
        weighted (f/lam [['target 'S]] (sum (weighted-inner 'target)))]
    {:name 'markov/nnrat-kernel-step-residual-weighted-expansion-bound :universes ['u]
     :type (f/forall bindings (le lhs (sum weighted)))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-transitive lhs (sum raw) (sum weighted)
            (poly 'markov/nnrat-kernel-step-residual-expansion-bound
                  'S 'states 'kernel 'left 'right)
            (poly 'nnrat/map-sum-monotone 'S raw weighted
                  (f/lam [['target 'S]]
                    (poly 'nnrat/map-sum-monotone 'S
                          (f/lam [['i 'S]]
                            (dist (f/app (flow (remainder :left) 'target) 'i)
                                  (f/app (flow (remainder :right) 'target) 'i)))
                          (weighted-inner 'target)
                          (f/lam [['i 'S]] (scaled-residual-bound 'i 'target))
                          (items)))
                  (items))))}))

(def theorem-specs [left-decomposition-spec right-decomposition-spec
                    residual-cancellation-spec residual-expansion-bound-spec
                    residual-weighted-expansion-bound-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-total-variation-translation rainbow.math.rational.nnrat.shared-residual-mass rainbow.math.rational.nnrat.ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-residual-expansion theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-residual-expansion))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
