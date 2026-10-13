(ns rainbow.math.finite.markov-column-exact-contraction
  "Exact column-minimum coefficient and its positive-total properness."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.complement-proper :as proper]
            [rainbow.math.finite.markov-minorization-complement :as exact]
            [rainbow.math.finite.markov-column-minorization :as column]
            [rainbow.math.finite.markov-dobrushin-contraction :as contraction]
            [rainbow.math.finite.markov-geometric-decay :as decay]
            [rainbow.math.finite.markov-geometric-convergence :as convergence]
            [rainbow.math.finite.markov-ergodic-uniqueness :as uniqueness]))

(def U [:param 'u])
(def one (f/const* 'nnrat/one []))
(defn- app [name & xs] (apply f/app (f/const* name []) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [U]) xs))
(defn- total [mass] (poly 'probability/nnrat-total-mass 'S 'states mass))
(defn- rate [mass] (app 'nnrat/distance (total mass) one))
(defn- positive [mass] (app 'nnrat/positive (total mass)))
(defn- member [x] (poly 'list/membership 'S (poly 'finset-data/enumeration 'S 'states) x))

(def minorization-exact-factor-proper-spec
  (let [bindings (conj exact/anchored-binders ['positive (positive 'lower-mass)])]
    {:name 'markov/nnrat-exact-minorization-factor-proper :universes ['u]
     :type (f/forall bindings (proper/proper (rate 'lower-mass)))
     :value (f/lam bindings
              (app 'nnrat/distance-to-one-proper-of-positive-at-most-one (total 'lower-mass)
                (poly 'markov/nnrat-minorizing-total-at-most-one
                      'S 'states 'kernel 'lower-mass 'normalized 'minorization 'anchor 'anchor-member)
                'positive))}))

(def column-bindings
  (into column/base-binders [['anchor-member (member 'anchor)] ['normalized column/normalized]]))
(def column-mass column/mass)
(def column-rate (rate column-mass))
(defn- column-minorizes []
  (poly 'markov/nnrat-column-minimum-mass-minorizes 'S 'states 'kernel 'anchor))
(def column-exact-coefficient-spec
  {:name 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum :universes ['u]
   :type (f/forall column-bindings
           (app 'signed/at-most (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
                (app 'signed/from-nnrat column-rate)))
   :value (f/lam column-bindings
            (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-minorization
                  'S 'states 'kernel column-mass 'normalized (column-minorizes) 'anchor 'anchor-member))})
(def column-exact-factor-proper-spec
  (let [bindings (conj column-bindings ['positive (positive column-mass)])]
    {:name 'markov/nnrat-exact-column-minimum-factor-proper :universes ['u]
     :type (f/forall bindings (proper/proper column-rate))
     :value (f/lam bindings
              (poly 'markov/nnrat-exact-minorization-factor-proper
                    'S 'states 'kernel column-mass 'normalized (column-minorizes) 'anchor 'anchor-member 'positive))}))
(def column-exact-contraction-spec
  "Apply the coefficient certificate to obtain the actual step-L1 bound.
  Positive shared total is required for strictness, not for this inequality."
  (let [nnrat (f/const* 'nnrat/NonnegativeRational [])
        bindings (into column-bindings
                       [['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]
                        ['equal-total (app 'nnrat/equivalent (total 'left) (total 'right))]])
        step (fn [mass] (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
        l1 (fn [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))]
    {:name 'markov/nnrat-exact-column-minimum-contraction :universes ['u]
     :type (f/forall bindings
             (app 'nnrat/at-most (l1 (step 'left) (step 'right))
                  (app 'nnrat/multiply column-rate (l1 'left 'right))))
     :value (f/lam bindings
              (poly 'markov/nnrat-dobrushin-contraction
                    'S 'states 'kernel column-rate 'normalized
                    (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum
                          'S 'states 'kernel 'anchor 'anchor-member 'normalized)
                    'left 'right 'equal-total))}))
(def column-exact-geometric-decay-spec
  "Specialize geometric TV decay to the exact column factor."
  (let [nnrat (f/const* 'nnrat/NonnegativeRational [])
        nat (f/const* 'data/Nat [])
        bindings (into column-bindings
                       [['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]
                        ['equal-total (app 'nnrat/equivalent (total 'left) (total 'right))]
                        ['steps nat]])
        iterate (fn [mass] (poly 'markov/nnrat-kernel-iterate 'S 'states 'kernel 'steps mass))
        tv (fn [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
        power (app 'nnrat/power column-rate 'steps)
        conclusion (app 'nnrat/at-most (tv (iterate 'left) (iterate 'right))
                        (app 'nnrat/multiply power (tv 'left 'right)))]
    {:name 'markov/nnrat-exact-column-minimum-geometric-decay :universes ['u]
     :type (f/forall bindings conclusion)
     :value (f/lam bindings
              (poly 'markov/nnrat-kernel-iterate-total-variation-decay
                    'S 'states 'kernel column-rate 'normalized
                    (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum
                          'S 'states 'kernel 'anchor 'anchor-member 'normalized)
                    'left 'right 'equal-total 'steps))}))
(def column-exact-stationary-uniqueness-spec
  "Specialize stationary uniqueness to a positive exact column factor."
  (let [nnrat (f/const* 'nnrat/NonnegativeRational [])
        mass (f/arrow 'S nnrat)
        stationary (fn [m] (poly 'markov/nnrat-stationary 'S 'states 'kernel m))
        state (f/const* 'S [])
        bindings (into column-bindings
                       [['positive (positive column-mass)]
                        ['proper (proper/proper column-rate)]
                        ['left mass] ['right mass]
                        ['left-stationary (stationary 'left)]
                        ['right-stationary (stationary 'right)]
                        ['equal-total (app 'nnrat/equivalent (total 'left) (total 'right))]
                        ['state 'S]
                        ['state-member (poly 'list/membership 'S
                                              (poly 'finset-data/enumeration 'S 'states) 'state)]])
        numerator (app 'nnrat/numerator column-rate)
        denominator-predecessor (app 'nnrat/denominator-predecessor column-rate)]
    {:name 'markov/nnrat-exact-column-minimum-stationary-pointwise-unique :universes ['u]
     :type (f/forall bindings (app 'nnrat/equivalent (f/app 'left 'state) (f/app 'right 'state)))
     :value (f/lam bindings
              (poly 'markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound
                    'S 'states 'kernel numerator denominator-predecessor
                    'proper 'normalized
                    (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum
                          'S 'states 'kernel 'anchor 'anchor-member 'normalized)
                    'left 'right 'left-stationary 'right-stationary 'equal-total
                    'state 'state-member))}))
(def column-exact-geometric-convergence-spec
  "Specialize the finite geometric convergence consumer to the exact column factor."
  (let [nnrat (f/const* 'nnrat/NonnegativeRational [])
        nat (f/const* 'data/Nat [])
        mass (f/arrow 'S nnrat)
        stationary (fn [m] (poly 'markov/nnrat-stationary 'S 'states 'kernel m))
        iterate (fn [m] (poly 'markov/nnrat-kernel-iterate 'S 'states 'kernel 'steps m))
        tv (fn [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
        bindings (into column-bindings
                       [['start mass] ['pi mass]
                        ['pi-stationary (stationary 'pi)]
                        ['equal-total (app 'nnrat/equivalent (total 'start) (total 'pi))]
                        ['steps nat]])
        conclusion (app 'nnrat/at-most (tv (iterate 'start) 'pi)
                        (app 'nnrat/multiply (app 'nnrat/power column-rate 'steps)
                              (tv 'start 'pi)))]
    {:name 'markov/nnrat-exact-column-minimum-geometric-convergence-to-stationary
     :universes ['u]
     :type (f/forall bindings conclusion)
     :value (f/lam bindings
              (poly 'markov/nnrat-kernel-iterate-geometric-convergence-to-stationary
                    'S 'states 'kernel column-rate 'normalized
                    (poly 'markov/signed-kernel-dobrushin-at-most-of-exact-column-minimum
                          'S 'states 'kernel 'anchor 'anchor-member 'normalized)
                    'start 'pi 'pi-stationary 'equal-total 'steps))}))
(def theorem-specs [minorization-exact-factor-proper-spec column-exact-coefficient-spec
                    column-exact-factor-proper-spec column-exact-contraction-spec
                    column-exact-geometric-decay-spec column-exact-stationary-uniqueness-spec
                    column-exact-geometric-convergence-spec])
(defn extend-environment [env]
  (-> env uniqueness/extend-environment convergence/extend-environment
      decay/extend-environment contraction/extend-environment column/extend-environment exact/extend-environment proper/extend-environment
      (support/extend-with :finite-markov-column-exact-contraction theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
