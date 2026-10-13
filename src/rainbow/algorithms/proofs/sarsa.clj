(ns rainbow.algorithms.proofs.sarsa
  "SARSA on-policy temporal-difference control over signed rationals. SARSA shares
  the temporal-difference update with Q-learning -- the new action value is the
  current value plus the learning rate times the TD error -- but bootstraps from
  the value of the action actually taken in the next state (on-policy) rather than
  from the greedy maximum (off-policy). So the SARSA update is exactly the shared
  Q-update fed the on-policy next value (AHoF D62); when that next value equals the
  greedy value the two updates coincide.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.sarsa`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- td-error [reward discount next current]
  (function/app (function/const* 'learning/signed-td-error [])
                reward discount next current))
(defn- q-update [rate reward discount next current]
  (function/app (function/const* 'learning/signed-q-update [])
                rate reward discount next current))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- sarsa-update [rate reward discount next-action-value current]
  (function/app (function/const* 'learning/signed-sarsa-update [])
                rate reward discount next-action-value current))

;; Definitions --------------------------------------------------------------

;; The SARSA update: current value plus rate times the on-policy TD error.
(def sarsa-update-spec
  {:name 'learning/signed-sarsa-update :kind :definition :universes []
   :type (function/arrow nnrat signed nnrat signed signed signed)
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat]
            ['next-action-value signed] ['current signed]]
           (signed-add 'current
                       (signed-scale 'rate
                                     (td-error 'reward 'discount
                                               'next-action-value 'current))))})

(def definition-specs [sarsa-update-spec])

;; Theorems -----------------------------------------------------------------

(def sarsa-update-unfold-spec
  {:name 'learning/signed-sarsa-update-unfold :universes []
   :type (function/forall
          [['rate nnrat] ['reward signed] ['discount nnrat]
           ['next-action-value signed] ['current signed]]
          (equality signed
                    (sarsa-update 'rate 'reward 'discount 'next-action-value
                                  'current)
                    (signed-add 'current
                                (signed-scale 'rate
                                              (td-error 'reward 'discount
                                                        'next-action-value
                                                        'current)))))
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat]
            ['next-action-value signed] ['current signed]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            signed (sarsa-update 'rate 'reward 'discount 'next-action-value
                                 'current)))})

;; SARSA and Q-learning share the update: given the same bootstrap value, the
;; on-policy SARSA update equals the Q-update. They differ only in whether that
;; value is the taken action's (SARSA) or the greedy maximum (Q-learning).
(def sarsa-equals-q-update-spec
  {:name 'learning/signed-sarsa-equals-q-update :universes []
   :type (function/forall
          [['rate nnrat] ['reward signed] ['discount nnrat]
           ['next-action-value signed] ['current signed]]
          (equality signed
                    (sarsa-update 'rate 'reward 'discount 'next-action-value
                                  'current)
                    (q-update 'rate 'reward 'discount 'next-action-value
                              'current)))
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat]
            ['next-action-value signed] ['current signed]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            signed (sarsa-update 'rate 'reward 'discount 'next-action-value
                                 'current)))})

(def theorem-specs [sarsa-update-unfold-spec sarsa-equals-q-update-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "SARSA expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :sarsa}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "SARSA declaration rejected"
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
