(ns rainbow.math.finite.markov-minorization-complement
  "Exact complementary-mass bounds, without a raw-denominator approximation.
  A listed normalized row bounds the shared total before taking its complement."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-minorization :as minorization]
            [rainbow.math.rational.nnrat.ordered-distance :as ordered]))

(def U [:param 'u])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def one (f/const* 'nnrat/one []))
(defn- app [name & xs] (apply f/app (f/const* name []) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [U]) xs))
(defn- enumeration [] (poly 'finset-data/enumeration 'S 'states))
(defn- member [x] (poly 'list/membership 'S (enumeration) x))
(defn- total [mass] (poly 'probability/nnrat-total-mass 'S 'states mass))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- add [a b] (app 'nnrat/add a b))
(defn- complement [mass] (app 'nnrat/distance mass one))
(def anchored-binders
  (into minorization/certificate-binders [['anchor 'S] ['anchor-member (member 'anchor)]]))

(def minorizing-total-at-most-one-spec
  (let [amount (total 'lower-mass) row (f/app 'kernel 'anchor) row-total (total row)]
    {:name 'markov/nnrat-minorizing-total-at-most-one :universes ['u]
     :type (f/forall anchored-binders (le amount one))
     :value (f/lam anchored-binders
              (app 'nnrat/at-most-transitive amount row-total one
                (poly 'nnrat/map-sum-monotone-on 'S 'lower-mass row (enumeration)
                  (f/lam [['column 'S] ['column-member (member 'column)]]
                    (f/app 'minorization 'anchor 'anchor-member 'column 'column-member)))
                (app 'nnrat/equivalent-to-at-most row-total one (f/app 'normalized 'anchor))))}))

(def exact-complement-budget-spec
  (let [bindings [['mass nnrat] ['bounded (le 'mass one)]]
        rho (complement 'mass) forward (add 'mass rho) backward (add rho 'mass)
        sum-is-one
        (app 'nnrat/equivalent-transitive backward forward one
          (app 'nnrat/add-commutative rho 'mass)
          (app 'nnrat/add-distance-of-at-most 'mass one 'bounded))]
    {:name 'nnrat/one-at-most-distance-complement-plus-mass :universes []
     :type (f/forall bindings (le one backward))
     :value (f/lam bindings
              (app 'nnrat/equivalent-to-at-most one backward
                (app 'nnrat/equivalent-symmetric backward one sum-is-one)))}))

(def exact-minorization-bound-spec
  (let [amount (total 'lower-mass) rho (complement amount)]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-exact-minorization :universes ['u]
     :type (f/forall anchored-binders
             (app 'signed/at-most
               (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
               (app 'signed/from-nnrat rho)))
     :value (f/lam anchored-binders
              (poly 'markov/signed-kernel-dobrushin-at-most-of-minorization
                'S 'states 'kernel 'lower-mass 'normalized 'minorization rho
                (app 'nnrat/one-at-most-distance-complement-plus-mass amount
                  (poly 'markov/nnrat-minorizing-total-at-most-one
                    'S 'states 'kernel 'lower-mass 'normalized 'minorization 'anchor 'anchor-member))))}))

(def theorem-specs [minorizing-total-at-most-one-spec exact-complement-budget-spec exact-minorization-bound-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-minorization rainbow.math.rational.nnrat.ordered-distance])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-minorization-complement theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-minorization-complement))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
