(ns rainbow.algorithms.proofs.ahof.exact-inference
  "AHoF D2 worked exact Bayesian inference by enumeration.

  A two-node binary network: a uniform prior over A in {0,1} and a conditional
  P(B|A). Enumerating the hidden variable A gives P(B=1) = 1/2*1/2 + 1/2*1 = 3/4
  and P(B=0) = 1/2*1/2 + 1/2*0 = 1/4, which sum to one. All values are exact
  rationals; the marginals are proved by cross-product reflexivity.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.exact-inference`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- equivalent-by-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- if-data [condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat condition decision then-value else-value))

(def grid (function/const* 'ahof-d2/grid []))
(def prior (function/const* 'ahof-d2/prior []))
(def likelihood-true (function/const* 'ahof-d2/likelihood-true []))
(def likelihood-false (function/const* 'ahof-d2/likelihood-false []))

(defn- marginal [likelihood]
  (function/app (function/const* 'inference/nnrat-marginal [zero-level])
                nat grid prior likelihood))

;; Definitions --------------------------------------------------------------

(def grid-spec
  {:name 'ahof-d2/grid :kind :definition :universes []
   :type (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
   :value (function/app (function/const* 'finset-data/range []) (data-nat 2))})

(def prior-spec
  {:name 'ahof-d2/prior :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['ignored-state nat]] nnrat-half)})

(defn- conditional-on-zero [then-value else-value]
  (function/lam
   [['state nat]]
   (if-data (nat-equality 'state (data-nat 0))
            (decide-nat-equality 'state (data-nat 0))
            then-value else-value)))

(def likelihood-true-spec
  {:name 'ahof-d2/likelihood-true :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (conditional-on-zero nnrat-half nnrat-one)})

(def likelihood-false-spec
  {:name 'ahof-d2/likelihood-false :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (conditional-on-zero nnrat-half nnrat-zero)})

(def marginal-true-spec
  {:name 'ahof-d2/marginal-true :kind :definition :universes []
   :type nnrat :value (marginal likelihood-true)})

(def marginal-false-spec
  {:name 'ahof-d2/marginal-false :kind :definition :universes []
   :type nnrat :value (marginal likelihood-false)})

(def definition-specs
  [grid-spec prior-spec likelihood-true-spec likelihood-false-spec
   marginal-true-spec marginal-false-spec])

;; Theorems -----------------------------------------------------------------

(def marginal-values-spec
  (let [mt (function/const* 'ahof-d2/marginal-true [])
        mf (function/const* 'ahof-d2/marginal-false [])
        three-quarters (make-rational (data-nat 3) (data-nat 3))
        one-quarter (make-rational (data-nat 1) (data-nat 3))
        at-true (equivalent mt three-quarters)
        at-false (equivalent mf one-quarter)]
    {:name 'ahof-d2/marginal-values :universes []
     :type (proposition/conjunction at-true at-false)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      at-true at-false
      (equivalent-by-cross mt three-quarters)
      (equivalent-by-cross mf one-quarter))}))

(def normalization-spec
  ;; Proved compositionally to keep every kernel reduction small: the two
  ;; marginals are each replaced by their exact literal (3/4 and 1/4) via
  ;; add-respects-equivalence, then 3/4 + 1/4 reduces to one by cross reflexivity.
  (let [mt (function/const* 'ahof-d2/marginal-true [])
        mf (function/const* 'ahof-d2/marginal-false [])
        three-quarters (make-rational (data-nat 3) (data-nat 3))
        one-quarter (make-rational (data-nat 1) (data-nat 3))
        total (add mt mf)
        literal-total (add three-quarters one-quarter)]
    {:name 'ahof-d2/normalization :universes []
     :type (equivalent total nnrat-one)
     :value
     (function/app
      (function/const* 'nnrat/equivalent-transitive [])
      total literal-total nnrat-one
      (function/app
       (function/const* 'nnrat/add-respects-equivalence [])
       mt three-quarters mf one-quarter
       (equivalent-by-cross mt three-quarters)
       (equivalent-by-cross mf one-quarter))
      (equivalent-by-cross literal-total nnrat-one))}))

(def exact-inference-spec
  (let [values (:type marginal-values-spec)
        normalization (:type normalization-spec)]
    {:name 'ahof-d2/exact-inference :universes []
     :type (proposition/conjunction values normalization)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      values normalization
      (function/const* 'ahof-d2/marginal-values [])
      (function/const* 'ahof-d2/normalization []))}))

(def theorem-specs
  [marginal-values-spec normalization-spec exact-inference-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF exact-inference expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :ahof-d2-exact-inference}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF exact-inference declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
