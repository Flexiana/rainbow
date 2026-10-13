(ns rainbow.algorithms.proofs.pattern-search
  "Generalized pattern search over exact rationals: a derivative-free poll that
  moves to the best of a set of candidate points. Each candidate carries an
  objective value; the poll picks the candidate with the smaller value (an argmin
  by decided comparison), and the move is accepted only when the polled best
  improves on the current objective. This is the poll-and-accept structure of
  pattern search (AHoF O35); no gradient is used, only objective comparisons.

  Scope (measured by the kernel): this module has 3 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.pattern-search`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))

(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; A self-contained documentation proposition for the if-data condition slot.
(defn- condition [decision]
  (function/equality type-level bool decision decision))

(defn- if-signed [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                signed (condition decision) decision then-value else-value))

(defn- poll-better [value-a value-b point-a point-b]
  (function/app (function/const* 'search/poll-better [])
                value-a value-b point-a point-b))
(defn- poll-improves [best-value current-value]
  (function/app (function/const* 'search/poll-improves []) best-value
                current-value))
(defn- pattern-move [best-value current-value best-point current-point]
  (function/app (function/const* 'search/pattern-move [])
                best-value current-value best-point current-point))

;; Definitions --------------------------------------------------------------

;; The poll picks the point with the smaller objective value (argmin of two).
(def poll-better-spec
  {:name 'search/poll-better :kind :definition :universes []
   :type (function/arrow nnrat nnrat signed signed signed)
   :value (function/lam [['value-a nnrat] ['value-b nnrat]
                         ['point-a signed] ['point-b signed]]
                        (if-signed (decide-at-most 'value-a 'value-b)
                                   'point-a 'point-b))})

;; The polled best improves the current point when its value is at most (and the
;; step accepts on a strict-enough improvement via the decided comparison).
(def poll-improves-spec
  {:name 'search/poll-improves :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['best-value nnrat] ['current-value nnrat]]
                        (decide-at-most 'best-value 'current-value))})

;; Move to the polled best if it improves, otherwise stay at the current point.
(def pattern-move-spec
  {:name 'search/pattern-move :kind :definition :universes []
   :type (function/arrow nnrat nnrat signed signed signed)
   :value (function/lam [['best-value nnrat] ['current-value nnrat]
                         ['best-point signed] ['current-point signed]]
                        (if-signed (poll-improves 'best-value 'current-value)
                                   'best-point 'current-point))})

(def definition-specs
  [poll-better-spec poll-improves-spec pattern-move-spec])

;; Theorems -----------------------------------------------------------------

(def poll-better-unfold-spec
  {:name 'search/poll-better-unfold :universes []
   :type (function/forall
          [['value-a nnrat] ['value-b nnrat] ['point-a signed]
           ['point-b signed]]
          (equality signed
                    (poll-better 'value-a 'value-b 'point-a 'point-b)
                    (if-signed (decide-at-most 'value-a 'value-b)
                               'point-a 'point-b)))
   :value (function/lam [['value-a nnrat] ['value-b nnrat] ['point-a signed]
                         ['point-b signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (poll-better 'value-a 'value-b 'point-a
                                             'point-b)))})

(def poll-improves-unfold-spec
  {:name 'search/poll-improves-unfold :universes []
   :type (function/forall
          [['best-value nnrat] ['current-value nnrat]]
          (equality bool (poll-improves 'best-value 'current-value)
                    (decide-at-most 'best-value 'current-value)))
   :value (function/lam [['best-value nnrat] ['current-value nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (poll-improves 'best-value 'current-value)))})

(def pattern-move-unfold-spec
  {:name 'search/pattern-move-unfold :universes []
   :type (function/forall
          [['best-value nnrat] ['current-value nnrat] ['best-point signed]
           ['current-point signed]]
          (equality signed
                    (pattern-move 'best-value 'current-value 'best-point
                                  'current-point)
                    (if-signed (poll-improves 'best-value 'current-value)
                               'best-point 'current-point)))
   :value (function/lam [['best-value nnrat] ['current-value nnrat]
                         ['best-point signed] ['current-point signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (pattern-move 'best-value 'current-value
                                              'best-point 'current-point)))})

(def theorem-specs
  [poll-better-unfold-spec poll-improves-unfold-spec pattern-move-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Pattern-search expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :pattern-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Pattern-search declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.pattern-search))
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
