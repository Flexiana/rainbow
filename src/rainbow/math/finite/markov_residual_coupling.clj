(ns rainbow.math.finite.markov-residual-coupling
  "Residual mass balance and constructive product-coupling marginals.
  The positive-mass coupling is p(i)*q(j)/M. Its marginals follow by
  finite-sum scaling and positive reciprocal cancellation. Positivity is
  explicit; the zero-mass case is not silently divided through."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-residual-expansion :as expansion]
            [rainbow.math.rational.nnrat.map-sum-scale :as scale]
            [rainbow.math.rational.division :as division]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (c 'nnrat/NonnegativeRational))
(def nat (c 'data/Nat))
(def base-binders
  [['S type-u] ['states (poly 'finset-data/Finset 'S)]
   ['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]])
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- items [] (poly 'finset-data/enumeration 'S 'states))
(defn- sum [mapping] (poly 'nnrat/map-sum 'S mapping (items)))
(defn- total [mapping] (poly 'probability/nnrat-total-mass 'S 'states mapping))
(defn residual-mapping [side]
  (f/lam [['i 'S]]
    (app (if (= side :left) 'nnrat/left-residual-mass 'nnrat/right-residual-mass)
         (f/app 'left 'i) (f/app 'right 'i))))
(defn- common []
  (f/lam [['i 'S]] (app 'minmax/min (f/app 'left 'i) (f/app 'right 'i))))

(defn- total-reconstruction [side]
  (let [r (residual-mapping side) common-mass (common)
        original (if (= side :left) 'left 'right)
        combined (f/lam [['i 'S]] (add (f/app r 'i) (f/app common-mass 'i)))
        lhs (add (total r) (total common-mass))
        pointwise
        (f/lam [['i 'S]]
          (trans (add (f/app r 'i) (f/app common-mass 'i))
                 (add (f/app common-mass 'i) (f/app r 'i)) (f/app original 'i)
                 (app 'nnrat/add-commutative (f/app r 'i) (f/app common-mass 'i))
                 (app (if (= side :left) 'nnrat/shared-plus-left-residual
                            'nnrat/shared-plus-right-residual)
                      (f/app 'left 'i) (f/app 'right 'i))))]
    (trans lhs (sum combined) (total original)
           (sym (sum combined) lhs (poly 'nnrat/map-sum-add 'S r common-mass (items)))
           (poly 'nnrat/map-sum-respects-equivalence 'S combined original pointwise (items)))))

(def left-residual-plus-common-total-spec
  {:name 'markov/nnrat-left-residual-plus-common-total :universes ['u]
   :type (f/forall base-binders
           (eqv (add (total (residual-mapping :left)) (total (common))) (total 'left)))
   :value (f/lam base-binders (total-reconstruction :left))})

(def residual-totals-equal-spec
  (let [bindings (conj base-binders ['same-total (eqv (total 'left) (total 'right))])
        p (total (residual-mapping :left)) q (total (residual-mapping :right))
        shared (total (common))
        pc (add p shared) qc (add q shared)]
    {:name 'markov/nnrat-residual-totals-equal :universes ['u]
     :type (f/forall bindings (eqv p q))
     :value
     (f/lam bindings
       (let [same (trans pc (total 'left) qc (total-reconstruction :left)
                         (trans (total 'left) (total 'right) qc 'same-total
                                (sym qc (total 'right) (total-reconstruction :right))))]
         (app 'nnrat/at-most-antisymmetric p q
              (app 'nnrat/at-most-add-right-cancel p shared q
                   (app 'nnrat/equivalent-to-at-most pc qc same))
              (app 'nnrat/at-most-add-right-cancel q shared p
                   (app 'nnrat/equivalent-to-at-most qc pc (sym pc qc same))))))}))

(def total-variation-residual-totals-spec
  (let [p (residual-mapping :left) q (residual-mapping :right)
        distances (f/lam [['i 'S]] (app 'nnrat/distance (f/app 'left 'i) (f/app 'right 'i)))
        sums (f/lam [['i 'S]] (add (f/app p 'i) (f/app q 'i)))
        lhs (poly 'markov/nnrat-total-variation 'S 'states 'left 'right)
        rhs (add (total p) (total q))]
    {:name 'markov/nnrat-total-variation-is-residual-total-sum :universes ['u]
     :type (f/forall base-binders (eqv lhs rhs))
     :value (f/lam base-binders
              (trans lhs (sum sums) rhs
                     (poly 'nnrat/map-sum-respects-equivalence 'S distances sums
                           (f/lam [['i 'S]]
                             (app 'nnrat/distance-is-residual-mass-sum
                                  (f/app 'left 'i) (f/app 'right 'i))) (items))
                     (poly 'nnrat/map-sum-add 'S p q (items))))}))

(def product-coupling-spec
  {:name 'markov/nnrat-product-coupling :kind :definition :universes ['u]
   :type (f/forall (conj base-binders ['normalizer nnrat]) (f/arrow 'S 'S nnrat))
   :value (f/lam (into base-binders [['normalizer nnrat] ['i 'S] ['j 'S]])
            (mul (mul (f/app 'left 'i) (f/app 'right 'j))
                 (app 'nnrat/reciprocal 'normalizer)))})
(defn- positive-mass [] (app 'nnrat/make (app 'data/succ 'ap) 'adp))
(defn- coupling [i j]
  (poly 'markov/nnrat-product-coupling 'S 'states 'left 'right (positive-mass) i j))

(defn- marginal-spec [left? name]
  (let [other (if left? 'right 'left)
        fixed (f/app (if left? 'left 'right) 'index)
        mass (positive-mass) inv (app 'nnrat/reciprocal mass)
        coefficient (mul fixed inv)
        mapping (f/lam [['i 'S]] (if left? (coupling 'index 'i) (coupling 'i 'index)))
        ordered (f/lam [['i 'S]] (mul (f/app other 'i) coefficient))
        normalized (mul (total other) coefficient)
        cancelled (mul (mul mass inv) fixed)
        bindings (into base-binders
                       [['ap nat] ['adp nat] ['other-total (eqv (total other) mass)] ['index 'S]])]
    {:name name :universes ['u]
     :type (f/forall bindings (eqv (sum mapping) fixed))
     :value
     (f/lam bindings
       (trans (sum mapping) (sum ordered) fixed
              (poly 'nnrat/map-sum-respects-equivalence 'S mapping ordered
                    (f/lam [['i 'S]]
                      (ring/equiv
                       (mul (if left? (mul fixed (f/app other 'i)) (mul (f/app other 'i) fixed)) inv)
                       (mul (f/app other 'i) coefficient))) (items))
              (trans (sum ordered) normalized fixed
                     (sym normalized (sum ordered)
                          (poly 'nnrat/map-sum-scale-right 'S other coefficient (items)))
                     (trans normalized (mul mass coefficient) fixed
                            (app 'nnrat/multiply-respects-equivalence
                                 (total other) mass coefficient coefficient 'other-total (refl coefficient))
                            (trans (mul mass coefficient) cancelled fixed
                                   (ring/equiv (mul mass coefficient) cancelled)
                                   (trans cancelled (mul (c 'nnrat/one) fixed) fixed
                                          (app 'nnrat/multiply-respects-equivalence
                                               (mul mass inv) (c 'nnrat/one) fixed fixed
                                               (app 'nnrat/divide-self-positive 'ap 'adp) (refl fixed))
                                          (app 'nnrat/multiply-one-left fixed)))))))}))

(def left-marginal-spec
  (marginal-spec true 'markov/nnrat-product-coupling-left-marginal))
(def right-marginal-spec
  (marginal-spec false 'markov/nnrat-product-coupling-right-marginal))
(def definition-specs [product-coupling-spec])
(def theorem-specs [left-residual-plus-common-total-spec
                    residual-totals-equal-spec total-variation-residual-totals-spec
                    left-marginal-spec right-marginal-spec])
(defn- add-if-missing [env spec]
  (if (environment/resolve-id env (:name spec)) env
      (support/add-spec env :finite-markov-residual-coupling-support spec)))
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-residual-expansion])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (add-if-missing scale/map-sum-scale-right-spec) (add-if-missing division/divide-self-positive-spec) (support/extend-with :finite-markov-residual-coupling (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-residual-coupling))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
