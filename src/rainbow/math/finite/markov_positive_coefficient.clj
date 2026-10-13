(ns rainbow.math.finite.markov-positive-coefficient
  "Explicit Dobrushin factors from a positive finite kernel minimum.
  Kernel-checked and axiom-free on D63. For minimum m=n/(d+1),
  use epsilon=1/(d+1) on one listed column and rho=d/(d+1). The bound
  need not be sharp. This module does not assert executable correctness."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.finite.markov-kernel-minimum :as minimum]
            [rainbow.math.finite.markov-overlap :as overlap]
            [rainbow.math.rational.nnrat.unit-fraction :as unit]))

(def U [:param 'u])
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- member [i]
  (poly 'list/membership 'S (poly 'finset-data/enumeration 'S 'states) i))
(defn- minimum-value []
  (poly 'markov/nnrat-kernel-minimum 'S 'states 'kernel 'initial-source 'initial-target))
(defn- predecessor [] (app 'nnrat/denominator-predecessor (minimum-value)))
(defn- factor [] (unit/proper-complement (predecessor)))
(defn- bound []
  (app 'signed/at-most
    (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
    (app 'signed/from-nnrat (factor))))
(def base-binders
  (into coefficient/base-binders
        [['normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel)]
         ['initial-source 'S] ['initial-target 'S]]))

(def coefficient-at-most-of-positive-minimum-spec
  (let [m (minimum-value) dp (predecessor)
        epsilon (unit/unit-fraction dp) rho (factor)
        one (f/const* 'nnrat/one []) sum (app 'nnrat/add rho epsilon)
        bindings (into base-binders
                       [['initial-target-member (member 'initial-target)]
                        ['minimum-positive (app 'nnrat/positive m)]])]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-positive-minimum :universes ['u]
     :type (f/forall bindings (bound))
     :value
     (f/lam bindings
       (poly 'markov/signed-kernel-dobrushin-at-most-of-shared-column
         'S 'states 'kernel 'normalized 'initial-target 'initial-target-member epsilon rho
         (f/lam [['i 'S] ['i-member (member 'i)]]
           (app 'nnrat/at-most-transitive epsilon m (f/app 'kernel 'i 'initial-target)
             (app 'nnrat/unit-fraction-at-most-positive m 'minimum-positive)
             (poly 'markov/nnrat-kernel-minimum-bounds-entry
               'S 'states 'kernel 'initial-source 'initial-target
               'i 'initial-target 'i-member 'initial-target-member)))
         (app 'nnrat/equivalent-to-at-most one sum
           (app 'nnrat/equivalent-symmetric sum one
             (app 'nnrat/unit-fraction-plus-complement dp)))))}))

(def listed-positive
  (f/forall [['source 'S] ['target 'S]
             ['source-member (member 'source)] ['target-member (member 'target)]]
    (app 'nnrat/positive (f/app 'kernel 'source 'target))))

(def coefficient-at-most-of-listed-positive-spec
  (let [bindings (into base-binders
                       [['initial-source-member (member 'initial-source)]
                        ['initial-target-member (member 'initial-target)]
                        ['listed-positive listed-positive]])]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-listed-positive :universes ['u]
     :type (f/forall bindings (bound))
     :value
     (f/lam bindings
       (poly 'markov/signed-kernel-dobrushin-at-most-of-positive-minimum
         'S 'states 'kernel 'normalized 'initial-source 'initial-target 'initial-target-member
         (poly 'markov/nnrat-kernel-minimum-positive
           'S 'states 'kernel 'initial-source 'initial-target
           'initial-source-member 'initial-target-member 'listed-positive)))}))

(def theorem-specs [coefficient-at-most-of-positive-minimum-spec
                    coefficient-at-most-of-listed-positive-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-overlap rainbow.math.rational.nnrat.unit-fraction rainbow.math.finite.markov-kernel-minimum])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-positive-coefficient theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-positive-coefficient))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
