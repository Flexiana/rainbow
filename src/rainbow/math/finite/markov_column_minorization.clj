(ns rainbow.math.finite.markov-column-minorization
  "Construct a shared lower mass by taking a finite minimum in each column.
  With a listed anchor it is the greatest listed minorizing mass pointwise.
  A positive computed total supplies a certified proper Dobrushin factor."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.rational-argmin :as argmin]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]
            [rainbow.math.finite.markov-minorization :as minorization]
            [rainbow.math.rational.nnrat.unit-fraction :as unit]))

(def U [:param 'u])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def one (f/const* 'nnrat/one []))
(defn- app [name & xs] (apply f/app (f/const* name []) xs))
(defn- poly [name & xs] (apply f/app (f/const* name [U]) xs))
(defn- member [x] (poly 'list/membership 'S (poly 'finset-data/enumeration 'S 'states) x))
(defn- score [column] (f/lam [['column-source 'S]] (f/app 'kernel 'column-source column)))
(defn- selected [column]
  (poly 'decision/finite-nnrat-argmin 'S 'states 'anchor (score column)))
(def mass (poly 'markov/nnrat-column-minimum-mass 'S 'states 'kernel 'anchor))
(def total (poly 'probability/nnrat-total-mass 'S 'states mass))
(def base-binders (conj coefficient/base-binders ['anchor 'S]))
(defn- minorizes [lower] (poly 'markov/nnrat-kernel-minorizes 'S 'states 'kernel lower))
(defn- bound [rho]
  (app 'signed/at-most (poly 'markov/signed-kernel-dobrushin-coefficient 'S 'states 'kernel)
       (app 'signed/from-nnrat rho)))

(def column-minimum-mass-spec
  {:name 'markov/nnrat-column-minimum-mass :kind :definition :universes ['u] :transparency :reducible
   :type (f/forall base-binders (f/arrow 'S nnrat))
   :value (f/lam (conj base-binders ['column 'S]) (f/app 'kernel (selected 'column) 'column))})

(def column-minimum-minorizes-spec
  {:name 'markov/nnrat-column-minimum-mass-minorizes :universes ['u]
   :type (f/forall base-binders (minorizes mass))
   :value (f/lam base-binders
            (f/lam [['source 'S] ['source-member (member 'source)]
                    ['column 'S] ['column-member (member 'column)]]
              (poly 'decision/finite-nnrat-argmin-dominates
                    'S 'states 'anchor (score 'column) 'source 'source-member)))})

(def column-minimum-greatest-spec
  (let [bindings (into base-binders [['anchor-member (member 'anchor)] ['lower-mass (f/arrow 'S nnrat)]
                                    ['minorization (minorizes 'lower-mass)]
                                    ['column 'S] ['column-member (member 'column)]])]
    {:name 'markov/nnrat-column-minimum-mass-greatest :universes ['u]
     :type (f/forall bindings (app 'nnrat/at-most (f/app 'lower-mass 'column) (f/app mass 'column)))
     :value (f/lam bindings
              (f/app 'minorization (selected 'column)
                (poly 'decision/finite-nnrat-argmin-is-member 'S 'states 'anchor (score 'column) 'anchor-member)
                'column 'column-member))}))

(def normalized (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel))
(def column-minimum-coefficient-bound-spec
  (let [bindings (into base-binders [['normalized normalized] ['rho nnrat]
                                    ['budget (app 'nnrat/at-most one (app 'nnrat/add 'rho total))]])]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-column-minimum-budget :universes ['u]
     :type (f/forall bindings (bound 'rho))
     :value (f/lam bindings
              (poly 'markov/signed-kernel-dobrushin-at-most-of-minorization
                    'S 'states 'kernel mass 'normalized
                    (poly 'markov/nnrat-column-minimum-mass-minorizes 'S 'states 'kernel 'anchor)
                    'rho 'budget))}))

(def positive-column-minimum-coefficient-bound-spec
  (let [rho (unit/proper-complement (app 'nnrat/denominator-predecessor total))
        bindings (into base-binders [['normalized normalized] ['positive (app 'nnrat/positive total)]])]
    {:name 'markov/signed-kernel-dobrushin-at-most-of-positive-column-minimum :universes ['u]
     :type (f/forall bindings (bound rho))
     :value (f/lam bindings
              (poly 'markov/signed-kernel-dobrushin-at-most-of-positive-minorization
                    'S 'states 'kernel mass 'normalized
                    (poly 'markov/nnrat-column-minimum-mass-minorizes 'S 'states 'kernel 'anchor)
                    'positive))}))

(def definition-specs [column-minimum-mass-spec])
(def theorem-specs [column-minimum-minorizes-spec column-minimum-greatest-spec
                    column-minimum-coefficient-bound-spec positive-column-minimum-coefficient-bound-spec])
(defn extend-environment [env]
  (-> env minorization/extend-environment argmin/extend-environment
      (support/extend-with :finite-markov-column-minorization (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
