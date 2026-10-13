(ns rainbow.math.finite.markov-total-variation-bound
  "Normalized finite total variation and its stochastic-row unit bound.

  The existing total-variation alias denotes L1. Here normalized TV is half
  that sum. Scalar domination by a+b lifts through the finite sum, giving
  L1(mu,nu) <= mass(mu)+mass(nu). Two unit masses therefore give TV <= 1.
  These bounds do not assert contraction or convergence."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.markov-total-variation :as variation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.map-sum-additive :as additive]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply]))

(def U [:param 'u])
(def type-level [:succ [:zero]])
(def type-u [:sort [:succ U]])
(defn- c [name] (function/const* name []))
(defn- app [f & xs] (apply function/app f xs))
(def nnrat (c 'nnrat/NonnegativeRational))
(def rzero (c 'nnrat/zero))
(def rone (c 'nnrat/one))
(def half (c 'nnrat/half))
(defn- add [a b] (app (c 'nnrat/add) a b))
(defn- mul [a b] (app (c 'nnrat/multiply) a b))
(defn- le [a b] (app (c 'nnrat/at-most) a b))
(defn- eqv [a b] (app (c 'nnrat/equivalent) a b))
(defn- refl [a] (app (c 'nnrat/equivalent-reflexive) a))
(defn- sym [a b p] (app (c 'nnrat/equivalent-symmetric) a b p))
(defn- le-refl [a] (app (c 'nnrat/at-most-reflexive) a))
(defn- trans [a b d p q] (app (c 'nnrat/at-most-transitive) a b d p q))
(defn- respects [a a' b b' pa pb p]
  (app (c 'nnrat/at-most-respects-equivalence) a a' b b' pa pb p))
(defn- distance [a b] (app (c 'nnrat/distance) a b))
(defn- finset [s] (app (function/const* 'finset-data/Finset [U]) s))
(defn- enumeration [s states]
  (app (function/const* 'finset-data/enumeration [U]) s states))
(defn- sum [s f xs] (app (function/const* 'nnrat/map-sum [U]) s f xs))
(defn- mass [s states f]
  (app (function/const* 'probability/nnrat-total-mass [U]) s states f))
(defn- l1 [s states f g]
  (app (function/const* 'markov/nnrat-total-variation [U]) s states f g))
(defn- tv [s states f g]
  (app (function/const* 'markov/nnrat-normalized-total-variation [U])
       s states f g))

(defn- below-add-left [a b]
  (respects a (add a rzero) (add a b) (add a b)
            (sym (add a rzero) a (app (c 'nnrat/add-zero-right) a))
            (refl (add a b))
            (app (c 'nnrat/add-monotone) a a rzero b
                 (le-refl a) (app (c 'nnrat/zero-at-most) b))))

(defn- below-add-right [a b]
  (respects b b (add a b) (add b a)
            (refl b) (app (c 'nnrat/add-commutative) a b)
            (below-add-left b a)))

(def distance-at-most-sum-spec
  {:name 'nnrat/distance-at-most-sum :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
           (le (distance 'a 'b) (add 'a 'b)))
   :value
   (function/lam [['a nnrat] ['b nnrat]]
     (let [total (add 'a 'b)]
       (app (c 'nnrat/distance-at-most-of-additive-closeness) 'a 'b total
            (trans 'a total (add 'b total)
                   (below-add-left 'a 'b) (below-add-right 'b total))
            (trans 'b total (add 'a total)
                   (below-add-right 'a 'b) (below-add-right 'a total)))))})

(def mass-binders
  [['S type-u] ['states (finset 'S)]
   ['left (function/arrow 'S nnrat)] ['right (function/arrow 'S nnrat)]])

(def normalized-total-variation-spec
  {:name 'markov/nnrat-normalized-total-variation
   :kind :definition :universes ['u]
   :type (function/forall mass-binders nnrat)
   :value (function/lam mass-binders
            (mul half (l1 'S 'states 'left 'right)))})

(def total-variation-at-most-mass-sum-spec
  (let [total (add (mass 'S 'states 'left) (mass 'S 'states 'right))
        delta (l1 'S 'states 'left 'right)
        mapping (function/lam [['state 'S]]
                  (add (app 'left 'state) (app 'right 'state)))
        distances (function/lam [['state 'S]]
                    (distance (app 'left 'state) (app 'right 'state)))
        states (enumeration 'S 'states)
        mapped (sum 'S mapping states)]
    {:name 'markov/nnrat-total-variation-at-most-mass-sum :universes ['u]
     :type (function/forall mass-binders (le delta total))
     :value
     (function/lam mass-binders
       (respects delta delta total mapped
                 (refl delta)
                 (sym mapped total
                      (app (function/const* 'nnrat/map-sum-add [U])
                           'S 'left 'right states))
                 (app (function/const* 'nnrat/map-sum-monotone [U])
                      'S distances mapping
                      (function/lam [['state 'S]]
                        (app (c 'nnrat/distance-at-most-sum)
                             (app 'left 'state) (app 'right 'state)))
                      states)))}))

(def half-times-two-spec
  (let [scaled (mul half (add rone rone))]
    {:name 'nnrat/half-times-two-equivalent-one :universes []
     :type (eqv scaled rone)
     :value (app (function/const* 'equality/reflexive [type-level])
                 (c 'data/Nat)
                 (app (c 'nat/multiply)
                      (app (c 'nnrat/numerator) scaled)
                      (app (c 'nnrat/denominator) rone)))}))

(def normalized-total-variation-at-most-one-spec
  (let [bindings (into mass-binders
                      [['left-normalized (eqv (mass 'S 'states 'left) rone)]
                       ['right-normalized (eqv (mass 'S 'states 'right) rone)]])
        lm (mass 'S 'states 'left) rm (mass 'S 'states 'right)
        total (add lm rm) two (add rone rone)
        delta (l1 'S 'states 'left 'right)]
    {:name 'markov/nnrat-normalized-total-variation-at-most-one :universes ['u]
     :type (function/forall bindings (le (tv 'S 'states 'left 'right) rone))
     :value
     (function/lam bindings
       (let [bounded
             (respects delta delta two total (refl delta)
                       (sym total two
                            (app (c 'nnrat/add-respects-equivalence)
                                 lm rone rm rone 'left-normalized 'right-normalized))
                       (app (function/const*
                             'markov/nnrat-total-variation-at-most-mass-sum [U])
                            'S 'states 'left 'right))]
         (respects (mul half delta) (mul half delta) rone (mul half two)
                   (refl (mul half delta))
                   (sym (mul half two) rone
                        (c 'nnrat/half-times-two-equivalent-one))
                   (app (c 'nnrat/multiply-monotone) half delta two bounded))))}))

(def row-total-variation-at-most-one-spec
  (let [bindings [['S type-u] ['states (finset 'S)]
                  ['kernel (function/arrow 'S 'S nnrat)]
                  ['normalized
                   (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
                        'S 'states 'kernel)]
                  ['x 'S] ['y 'S]]]
    {:name 'markov/row-total-variation-at-most-one :universes ['u]
     :type (function/forall bindings
             (le (tv 'S 'states (app 'kernel 'x) (app 'kernel 'y)) rone))
     :value
     (function/lam bindings
       (app (function/const* 'markov/nnrat-normalized-total-variation-at-most-one [U])
            'S 'states (app 'kernel 'x) (app 'kernel 'y)
            (app 'normalized 'x) (app 'normalized 'y)))}))

(def definition-specs [normalized-total-variation-spec])
(def theorem-specs [distance-at-most-sum-spec total-variation-at-most-mass-sum-spec
                    half-times-two-spec normalized-total-variation-at-most-one-spec
                    row-total-variation-at-most-one-spec])

(defn- extend-if-missing [env marker extend]
  (if (environment/resolve-id env marker) env (extend env)))

(defn extend-environment [env]
  (-> env
      variation/extend-environment
      (extend-if-missing 'nnrat/map-sum-add additive/extend-environment)
      (extend-if-missing 'nnrat/multiply-monotone multiply/extend-environment)
      (support/extend-with :finite-markov-total-variation-bound
                           (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
