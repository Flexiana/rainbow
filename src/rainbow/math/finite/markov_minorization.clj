(ns rainbow.math.finite.markov-minorization
  "Finite shared lower-mass certificates for Dobrushin bounds.
  A minorizing mass may vanish on some columns, so this does not require
  full positivity of the kernel. Statements concern the listed support."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.finite.markov-overlap :as overlap]
            [rainbow.math.rational.nnrat.unit-fraction :as unit]))

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
(defn- common-map [a b]
  (f/lam [['minorization-column 'S]]
    (app 'minmax/min (f/app a 'minorization-column) (f/app b 'minorization-column))))
(defn- dominated [mass]
  (f/forall [['x 'S] ['x-member (member 'x)]] (le (f/app 'lower-mass 'x) (f/app mass 'x))))
(defn- coefficient-bound [rho]
  (app 'signed/at-most (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
       (app 'signed/from-nnrat rho)))
(def row-pair [['source 'S] ['source-member (member 'source)]
               ['destination 'S] ['destination-member (member 'destination)]])
(def minorization-binders (conj coefficient/base-binders ['lower-mass (f/arrow 'S nnrat)]))
(def minorizes (poly 'markov/nnrat-kernel-minorizes 'S 'states 'kernel 'lower-mass))

(def minorizes-spec
  {:name 'markov/nnrat-kernel-minorizes :kind :definition :universes ['u] :transparency :reducible
   :type (f/forall minorization-binders 'Prop)
   :value (f/lam minorization-binders
            (f/forall row-pair
              (le (f/app 'lower-mass 'destination) (f/app 'kernel 'source 'destination))))})

(def common-total-at-least-minorizing-mass-spec
  (let [bindings [['S [:sort [:succ U]]] ['states (poly 'finset-data/Finset 'S)]
                  ['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]
                  ['lower-mass (f/arrow 'S nnrat)]
                  ['lower-left (dominated 'left)] ['lower-right (dominated 'right)]]
        common (common-map 'left 'right)]
    {:name 'markov/nnrat-common-total-at-least-minorizing-mass :universes ['u]
     :type (f/forall bindings (le (total 'lower-mass) (total common)))
     :value (f/lam bindings
              (poly 'nnrat/map-sum-monotone-on 'S 'lower-mass common (enumeration)
                (f/lam [['x 'S] ['x-member (member 'x)]]
                  (app 'minmax/at-most-min (f/app 'lower-mass 'x) (f/app 'left 'x) (f/app 'right 'x)
                       (f/app 'lower-left 'x 'x-member) (f/app 'lower-right 'x 'x-member)))))}))

(def certificate-binders
  (into minorization-binders
        [['normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel)]
         ['minorization minorizes]]))

(def coefficient-at-most-of-minorization-spec
  (let [mass (total 'lower-mass)
        bindings (into certificate-binders [['rho nnrat] ['budget (le one (add 'rho mass))]])
        rows [['i 'S] ['i-member (member 'i)] ['j 'S] ['j-member (member 'j)]]
        a (f/app 'kernel 'i) b (f/app 'kernel 'j) common (total (common-map a b))]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-minorization :universes ['u]
     :type (f/forall bindings (coefficient-bound 'rho))
     :value (f/lam bindings
              (poly 'markov/signed-kernel-dobrushin-at-most-of-common-mass
                'S 'states 'kernel 'normalized 'rho
                (f/lam rows
                  (app 'nnrat/at-most-transitive one (add 'rho mass) (add 'rho common) 'budget
                    (app 'nnrat/add-monotone 'rho 'rho mass common (app 'nnrat/at-most-reflexive 'rho)
                      (poly 'markov/nnrat-common-total-at-least-minorizing-mass 'S 'states a b 'lower-mass
                        (f/lam [['x 'S] ['x-member (member 'x)]]
                          (f/app 'minorization 'i 'i-member 'x 'x-member))
                        (f/lam [['x 'S] ['x-member (member 'x)]]
                          (f/app 'minorization 'j 'j-member 'x 'x-member))))))))}))

(def coefficient-at-most-of-positive-minorization-spec
  (let [mass (total 'lower-mass) dp (app 'nnrat/denominator-predecessor mass)
        epsilon (unit/unit-fraction dp) rho (unit/proper-complement dp)
        sum (add rho epsilon)
        bindings (conj certificate-binders ['positive (app 'nnrat/positive mass)])]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-positive-minorization :universes ['u]
     :type (f/forall bindings (coefficient-bound rho))
     :value (f/lam bindings
              (poly 'markov/signed-kernel-dobrushin-at-most-of-minorization
                'S 'states 'kernel 'lower-mass 'normalized 'minorization rho
                (app 'nnrat/at-most-transitive one sum (add rho mass)
                  (app 'nnrat/equivalent-to-at-most one sum
                    (app 'nnrat/equivalent-symmetric sum one (app 'nnrat/unit-fraction-plus-complement dp)))
                  (app 'nnrat/add-monotone rho rho epsilon mass (app 'nnrat/at-most-reflexive rho)
                       (app 'nnrat/unit-fraction-at-most-positive mass 'positive)))))}))

(def definition-specs [minorizes-spec])
(def theorem-specs [common-total-at-least-minorizing-mass-spec coefficient-at-most-of-minorization-spec
                    coefficient-at-most-of-positive-minorization-spec])
(defn extend-environment [env]
  (-> env overlap/extend-environment unit/extend-environment
      (support/extend-with :finite-markov-minorization (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
