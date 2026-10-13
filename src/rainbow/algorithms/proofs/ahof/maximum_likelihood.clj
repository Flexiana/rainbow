(ns rainbow.algorithms.proofs.ahof.maximum-likelihood
  "AHoF D10 worked maximum likelihood estimation over exact rationals. Two models
  are scored on a two-point data set by their per-datum log-likelihoods: model A
  scores 3/4 and 3/4 (total 3/2), model B scores 1/4 and 1/4 (total 1/2). Maximum
  likelihood prefers model A, since its total 3/2 is at least model B's 1/2. The
  totals are proved by cross-product equivalence and the preference by reflexivity
  of the decided comparison.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.maximum-likelihood`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def score-list (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))
(def one-quarter (make-rational (data-nat 1) (data-nat 3)))
(def three-halves (make-rational (data-nat 3) (data-nat 1)))
(def half (make-rational (data-nat 1) (data-nat 1)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))

(defn- nil-scores []
  (function/app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-score [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))

(def model-a-scores (function/const* 'ahof-d10/model-a-scores []))
(def model-b-scores (function/const* 'ahof-d10/model-b-scores []))

(defn- log-likelihood-total [scores]
  (function/app (function/const* 'estimation/log-likelihood-total []) scores))
(defn- mle-prefers [total-a total-b]
  (function/app (function/const* 'estimation/mle-prefers []) total-a total-b))

;; Definitions --------------------------------------------------------------

(def model-a-scores-spec
  {:name 'ahof-d10/model-a-scores :kind :definition :universes []
   :type score-list
   :value (cons-score three-quarters (cons-score three-quarters (nil-scores)))})

(def model-b-scores-spec
  {:name 'ahof-d10/model-b-scores :kind :definition :universes []
   :type score-list
   :value (cons-score one-quarter (cons-score one-quarter (nil-scores)))})

(def model-a-total-spec
  {:name 'ahof-d10/model-a-total :kind :definition :universes []
   :type nnrat :value (log-likelihood-total model-a-scores)})

(def model-b-total-spec
  {:name 'ahof-d10/model-b-total :kind :definition :universes []
   :type nnrat :value (log-likelihood-total model-b-scores)})

(def definition-specs
  [model-a-scores-spec model-b-scores-spec model-a-total-spec
   model-b-total-spec])

;; Theorems -----------------------------------------------------------------

;; Model A's total log-likelihood is 3/2.
(def model-a-total-is-three-halves-spec
  {:name 'ahof-d10/model-a-total-is-three-halves :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d10/model-a-total [])
                           three-halves)
   :value (equivalent-cross (function/const* 'ahof-d10/model-a-total [])
                            three-halves)})

;; Model B's total log-likelihood is 1/2.
(def model-b-total-is-one-half-spec
  {:name 'ahof-d10/model-b-total-is-one-half :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d10/model-b-total []) half)
   :value (equivalent-cross (function/const* 'ahof-d10/model-b-total []) half)})

;; Maximum likelihood prefers model A over model B.
(def prefers-a-spec
  {:name 'ahof-d10/mle-prefers-model-a :universes []
   :type (bool-equality
          (mle-prefers (function/const* 'ahof-d10/model-a-total [])
                       (function/const* 'ahof-d10/model-b-total []))
          bool-true)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool bool-true)})

(def maximum-likelihood-spec
  (let [a-law (:type model-a-total-is-three-halves-spec)
        b-law (:type model-b-total-is-one-half-spec)
        prefers-law (:type prefers-a-spec)]
    {:name 'ahof-d10/maximum-likelihood :universes []
     :type (proposition/conjunction
            a-law (proposition/conjunction b-law prefers-law))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      a-law (proposition/conjunction b-law prefers-law)
      (function/const* 'ahof-d10/model-a-total-is-three-halves [])
      (function/app
       (function/const* 'proposition/conjoin [])
       b-law prefers-law
       (function/const* 'ahof-d10/model-b-total-is-one-half [])
       (function/const* 'ahof-d10/mle-prefers-model-a [])))}))

(def theorem-specs
  [model-a-total-is-three-halves-spec model-b-total-is-one-half-spec
   prefers-a-spec maximum-likelihood-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF maximum-likelihood expression failed elaboration"
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
          {:origin :native :producer :ahof-d10-maximum-likelihood}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF maximum-likelihood declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.maximum-likelihood))
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
