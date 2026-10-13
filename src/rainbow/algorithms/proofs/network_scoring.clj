(ns rainbow.algorithms.proofs.network-scoring
  "Additive scoring of a Bayesian network. A decomposable score (BIC/BDeu style)
  is the sum of a per-node local score over the network's nodes: map the local
  score over the nodes, then reduce by addition. Because the score decomposes,
  adding a node adds only its local score -- the property that makes local
  structure search tractable.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.network-scoring`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def node-list (function/app (function/const* 'data/List [type-level]) nat))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- total-score [local nodes]
  (function/app (function/const* 'scoring/nnrat-total-score []) local nodes))

;; Definitions --------------------------------------------------------------

(def total-score-spec
  {:name 'scoring/nnrat-total-score :kind :definition :universes []
   :type (function/arrow (function/arrow nat nnrat) node-list nnrat)
   :value (function/lam
           [['local (function/arrow nat nnrat)] ['nodes node-list]]
           (function/app
            (function/const* 'list/nnrat-map-sum [zero-level])
            nat 'local 'nodes))})

(def definition-specs [total-score-spec])

;; Theorems -----------------------------------------------------------------

(def score-empty-spec
  {:name 'scoring/score-empty :universes []
   :type (function/forall
          [['local (function/arrow nat nnrat)]]
          (equality nnrat
                    (total-score 'local
                                 (function/app (function/const* 'data/nil
                                                                [type-level])
                                               nat))
                    nnrat-zero))
   :value (function/lam
           [['local (function/arrow nat nnrat)]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat nnrat-zero))})

;; The decomposition law: scoring a node list adds the head's local score to the
;; score of the remaining nodes.
(def score-cons-spec
  {:name 'scoring/score-cons :universes []
   :type (function/forall
          [['local (function/arrow nat nnrat)] ['head nat] ['tail node-list]]
          (equality nnrat
                    (total-score 'local
                                 (function/app
                                  (function/const* 'data/cons [type-level])
                                  nat 'head 'tail))
                    (nnrat-add (function/app 'local 'head)
                               (total-score 'local 'tail))))
   :value (function/lam
           [['local (function/arrow nat nnrat)] ['head nat] ['tail node-list]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (nnrat-add (function/app 'local 'head)
                             (total-score 'local 'tail))))})

(def theorem-specs [score-empty-spec score-cons-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Network-scoring expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :network-scoring}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Network-scoring declaration rejected"
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
