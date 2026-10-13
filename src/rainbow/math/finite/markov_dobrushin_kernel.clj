(ns rainbow.math.finite.markov-dobrushin-kernel
  "Dobrushin coefficient constructed from every pair of enumerated kernel rows.

  Two finite maxima compute max_{x,y} TV(Kx,Ky), where TV is half-L1.
  The coefficient dominates every enumerated row pair, is nonnegative, and
  is at most one for normalized stochastic rows. No mixing estimate is assumed
  or proved in this module."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.markov-total-variation-bound :as row-bound]
            [rainbow.math.finite.nnrat-sup-distance :as finite-sup]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.geometric-bridge :as embedding]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]
            [rainbow.math.rational.signed.rational :as rational]
            [rainbow.math.rational.signed.order :as order]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.rational.signed.order-transitivity :as transitivity]
            [rainbow.math.rational.signed.order-respects :as respects]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.rational.signed.vector-sup-distance :as fold]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [name] (f/const* name []))
(defn- app [g & xs] (apply f/app g xs))
(def nnrat (c 'nnrat/NonnegativeRational))
(def signed (c 'signed/SignedRational))
(def szero (c 'signed/zero))
(def sone (c 'signed/one))
(defn- le [a b] (app (c 'signed/at-most) a b))
(defn- finset [s] (app (f/const* 'finset-data/Finset [U]) s))
(defn- enumeration [s states]
  (app (f/const* 'finset-data/enumeration [U]) s states))
(defn- member [s states x]
  (app (f/const* 'list/membership [U]) s (enumeration s states) x))
(defn- map-max [s mapping states]
  (app (f/const* 'list/signed-map-max [U]) s mapping (enumeration s states)))
(defn- normalized [s states kernel]
  (app (f/const* 'markov/nnrat-kernel-rows-normalized [U]) s states kernel))
(defn- tv [s states kernel x y]
  (app (f/const* 'markov/nnrat-normalized-total-variation [U])
       s states (app kernel x) (app kernel y)))
(defn- row-distance [s states kernel x y]
  (app (c 'signed/from-nnrat) (tv s states kernel x y)))
(defn- row-mapping [s states kernel x]
  (f/lam [['y s]] (row-distance s states kernel x 'y)))
(defn- outer-mapping [s states kernel]
  (f/lam [['x s]] (map-max s (row-mapping s states kernel 'x) states)))
(defn- coefficient [s states kernel]
  (app (f/const* 'markov/signed-kernel-dobrushin-coefficient [U]) s states kernel))
(def base-binders
  [['S type-u] ['states (finset 'S)] ['kernel (f/arrow 'S 'S nnrat)]])
(defn- pair-binders []
  [['x 'S] ['x-member (member 'S 'states 'x)]
   ['y 'S] ['y-member (member 'S 'states 'y)]])
(defn- pairwise-bound [upper]
  (f/forall (pair-binders) (le (row-distance 'S 'states 'kernel 'x 'y) upper)))

(def kernel-coefficient-spec
  {:name 'markov/signed-kernel-dobrushin-coefficient
   :kind :definition :universes ['u]
   :type (f/forall base-binders signed)
   :value (f/lam base-binders
            (map-max 'S (outer-mapping 'S 'states 'kernel) 'states))})

(def kernel-coefficient-nonnegative-spec
  {:name 'markov/signed-kernel-dobrushin-coefficient-nonnegative :universes ['u]
   :type (f/forall base-binders (le szero (coefficient 'S 'states 'kernel)))
   :value (f/lam base-binders
            (app (f/const* 'list/signed-map-max-nonnegative [U])
                 'S (outer-mapping 'S 'states 'kernel) (enumeration 'S 'states)))})

(def kernel-coefficient-bounded-spec
  (let [bindings (into base-binders
                      [['upper signed] ['zero-upper (le szero 'upper)]
                       ['pointwise (pairwise-bound 'upper)]])]
    {:name 'markov/signed-kernel-dobrushin-coefficient-bounded :universes ['u]
     :type (f/forall bindings (le (coefficient 'S 'states 'kernel) 'upper))
     :value
     (f/lam bindings
       (app (f/const* 'list/signed-map-max-bounded [U])
            'S (outer-mapping 'S 'states 'kernel) 'upper 'zero-upper
            (enumeration 'S 'states)
            (f/lam [['x 'S] ['x-member (member 'S 'states 'x)]]
              (app (f/const* 'list/signed-map-max-bounded [U])
                   'S (row-mapping 'S 'states 'kernel 'x) 'upper 'zero-upper
                   (enumeration 'S 'states)
                   (f/lam [['y 'S] ['y-member (member 'S 'states 'y)]]
                     (app 'pointwise 'x 'x-member 'y 'y-member))))))}))

(def kernel-coefficient-at-most-one-spec
  (let [bindings (conj base-binders ['normalized (normalized 'S 'states 'kernel)])]
    {:name 'markov/signed-kernel-dobrushin-coefficient-at-most-one :universes ['u]
     :type (f/forall bindings (le (coefficient 'S 'states 'kernel) sone))
     :value
     (f/lam bindings
       (app (f/const* 'markov/signed-kernel-dobrushin-coefficient-bounded [U])
            'S 'states 'kernel sone (c 'signed/zero-at-most-one)
            (f/lam (pair-binders)
              (app (c 'signed/from-nnrat-at-most)
                   (tv 'S 'states 'kernel 'x 'y) (c 'nnrat/one)
                   (app (f/const* 'markov/row-total-variation-at-most-one [U])
                        'S 'states 'kernel 'normalized 'x 'y)))))}))

(def row-distance-at-most-coefficient-spec
  (let [bindings (into base-binders (pair-binders))
        inner (map-max 'S (row-mapping 'S 'states 'kernel 'x) 'states)
        delta (coefficient 'S 'states 'kernel)]
    {:name 'markov/row-distance-at-most-dobrushin-coefficient :universes ['u]
     :type (f/forall bindings (le (row-distance 'S 'states 'kernel 'x 'y) delta))
     :value
     (f/lam bindings
       (app (c 'signed/at-most-transitive)
            (row-distance 'S 'states 'kernel 'x 'y) inner delta
            (app (f/const* 'list/signed-map-max-upper-bound [U])
                 'S (row-mapping 'S 'states 'kernel 'x)
                 (enumeration 'S 'states) 'y 'y-member)
            (app (f/const* 'list/signed-map-max-upper-bound [U])
                 'S (outer-mapping 'S 'states 'kernel)
                 (enumeration 'S 'states) 'x 'x-member)))}))

(def definition-specs [kernel-coefficient-spec])
(def theorem-specs [kernel-coefficient-nonnegative-spec kernel-coefficient-bounded-spec
                    kernel-coefficient-at-most-one-spec row-distance-at-most-coefficient-spec])

(defn- add-if-missing [env producer spec]
  (if (environment/resolve-id env (:name spec)) env
      (support/extend-with env producer [spec])))
(defn- add-specs [env producer specs]
  (reduce #(add-if-missing %1 producer %2) env specs))
(defn extend-environment [env]
  (-> env
      row-bound/extend-environment
      (add-specs :signed-rational (concat rational/definition-specs rational/theorem-specs))
      (add-specs :signed-order (concat order/definition-specs order/theorem-specs))
      cancellation/extend-environment
      (add-if-missing :signed-equivalence-laws equivalence/equivalent-symmetric-spec)
      (add-if-missing :signed-order-transitivity transitivity/at-most-transitive-spec)
      (add-if-missing :signed-order-respects respects/at-most-respects-equivalence-spec)
      minmax/extend-environment
      (add-if-missing :signed-unit-laws units/zero-at-most-one-spec)
      (add-specs :signed-vector-sup-distance
                 [fold/signed-map-max-spec fold/signed-map-max-nonnegative-spec
                  fold/signed-map-max-bounded-spec fold/signed-equivalent-of-equality-spec])
      (add-if-missing :signed-geometric-bridge embedding/from-nnrat-at-most-spec)
      (add-if-missing :finite-nnrat-sup-distance finite-sup/signed-map-max-upper-bound-spec)
      (support/extend-with :finite-markov-dobrushin-kernel
                           (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
