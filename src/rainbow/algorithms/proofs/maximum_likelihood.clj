(ns rainbow.algorithms.proofs.maximum-likelihood
  "Maximum likelihood estimation over exact rationals. The log-likelihood of a
  model on a data set is the sum of the per-datum log-likelihoods (map then
  reduce); maximum likelihood estimation selects the model whose total
  log-likelihood is largest. This composes the exact-rational list sum with the
  decidable rational comparison (AHoF D10): scoring each model by its total
  log-likelihood and preferring the higher-scoring one.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.maximum-likelihood`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def score-list (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- score-total [scores]
  (function/app (function/const* 'list/nnrat-map-sum [zero-level])
                nnrat (function/lam [['score nnrat]] 'score) scores))
(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- log-likelihood-total [scores]
  (function/app (function/const* 'estimation/log-likelihood-total []) scores))
(defn- mle-prefers [total-a total-b]
  (function/app (function/const* 'estimation/mle-prefers []) total-a total-b))

;; Definitions --------------------------------------------------------------

;; The total log-likelihood: sum of the per-datum log-likelihoods.
(def log-likelihood-total-spec
  {:name 'estimation/log-likelihood-total :kind :definition :universes []
   :type (function/arrow score-list nnrat)
   :value (function/lam [['scores score-list]] (score-total 'scores))})

;; Maximum likelihood prefers the first model when its total is at least the
;; second's (the second's total is at most the first's).
(def mle-prefers-spec
  {:name 'estimation/mle-prefers :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['total-a nnrat] ['total-b nnrat]]
                        (decide-at-most 'total-b 'total-a))})

(def definition-specs [log-likelihood-total-spec mle-prefers-spec])

;; Theorems -----------------------------------------------------------------

(def log-likelihood-total-unfold-spec
  {:name 'estimation/log-likelihood-total-unfold :universes []
   :type (function/forall
          [['scores score-list]]
          (equality nnrat (log-likelihood-total 'scores)
                    (score-total 'scores)))
   :value (function/lam [['scores score-list]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (log-likelihood-total 'scores)))})

(def mle-prefers-unfold-spec
  {:name 'estimation/mle-prefers-unfold :universes []
   :type (function/forall
          [['total-a nnrat] ['total-b nnrat]]
          (equality bool (mle-prefers 'total-a 'total-b)
                    (decide-at-most 'total-b 'total-a)))
   :value (function/lam [['total-a nnrat] ['total-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (mle-prefers 'total-a 'total-b)))})

(def theorem-specs
  [log-likelihood-total-unfold-spec mle-prefers-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Maximum-likelihood expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :maximum-likelihood}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Maximum-likelihood declaration rejected"
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
