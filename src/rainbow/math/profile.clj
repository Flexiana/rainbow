(ns rainbow.math.profile
  "Explicit, opt-in logical assumption profiles.

  Principles are ordinary axiom declarations whose IDs flow through the
  kernel's dependency closure. Profiles change an environment's assumptions,
  never the kernel, and proof transactions must still allow the exact IDs.

  `classify-declaration` and `classify-cohort` add automated target
  classification: they read the axiom closure the kernel already computes and
  the provenance an activation already recorded, and name the smallest profile
  that covers a target. Classification is pure observation -- it adds nothing to
  the environment, so it cannot extend the trusted base -- and an axiom that is
  not a declared principle is reported as unknown and blocks any profile claim,
  because silently ignoring it would be exactly the silent extension the V1.1
  requirement forbids."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def principle-specs
  [{:name 'logic/excluded-middle
    :principle :classical
    :description "Every proposition is true or false."
    :universes []
    :type
    (proposition/forall
     [['claim 'Prop]]
     (proposition/disjunction 'claim (proposition/negation 'claim)))}

   {:name 'logic/proposition-extensionality
    :principle :propositional-extensionality
    :description "Logically equivalent propositions are equal."
    :universes []
    :type
    (proposition/forall
     [['left 'Prop :implicit] ['right 'Prop :implicit]
      ['equivalent (proposition/equivalence 'left 'right)]]
     (proposition/equality [:succ [:zero]] 'Prop 'left 'right))}

   {:name 'logic/proof-irrelevance
    :principle :proof-irrelevance
    :description "Any two proofs of the same proposition are equal."
    :universes []
    :type
     (proposition/forall
     [['claim 'Prop :implicit] ['left 'claim] ['right 'claim]]
     (proposition/equality [:zero] 'claim 'left 'right))}

   {:name 'logic/function-extensionality
    :principle :function-extensionality
    :description "Pointwise equal functions are equal."
    :universes ['u 'v]
    :type
    (let [u [:param 'u]
          v [:param 'v]
          sort-u [:sort u]
          sort-v [:sort v]
          function-type (proposition/arrow 'A 'B)]
      (proposition/forall
       [['A sort-u] ['B sort-v]
        ['left function-type] ['right function-type]
        ['pointwise
         (proposition/forall
          [['value 'A]]
          (proposition/equality
           v 'B (proposition/app 'left 'value)
           (proposition/app 'right 'value)))]]
       (proposition/equality [:imax u v] function-type 'left 'right)))}

   {:name 'logic/choice
    :principle :choice
    :description "A witness may be extracted from a propositional existence."
    :universes ['u]
    :type
    (let [u [:param 'u]]
      (proposition/forall
       [['A [:sort u]]
        ['P (proposition/arrow 'A 'Prop)]
        ['evidence (proposition/existence u 'A 'P)]]
       'A))}])

(def profiles
  {:constructive
   {:profile/principles #{}
    :profile/claim "No additional logical assumptions."}

   :classical
   {:profile/principles #{:classical}
    :profile/claim "Excluded middle only."}

   :propositional-extensional
   {:profile/principles #{:propositional-extensionality}
    :profile/claim "Propositional extensionality only."}

   :proof-irrelevant
   {:profile/principles #{:proof-irrelevance}
    :profile/claim "Proof irrelevance only."}

   :function-extensional
   {:profile/principles #{:function-extensionality}
    :profile/claim "Function extensionality only."}

   :choice-bearing
   {:profile/principles #{:choice}
    :profile/claim "Choice only."}

   :mathlib-complete-logic
   {:profile/principles #{:classical :function-extensionality
                          :propositional-extensionality :proof-irrelevance}
    :profile/claim
    "Rainbow's current explicit Mathlib-facing logical assumption set;
     not claimed equivalent to Lean's complete axiom profile."}

   :mathlib-logic
   {:profile/principles #{:classical :propositional-extensionality
                          :proof-irrelevance}
    :profile/claim
    "Current Rainbow logic assumptions often needed by Mathlib statements;
     not claimed equivalent to Lean's complete axiom profile."}})

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (reject! :logic-profile/elaboration-failed
               "Logical principle failed elaboration"
               {:surface surface :result result}))
    (:term result)))

(defn- add-principle [checked-environment spec profile]
  (let [type (elaborate! checked-environment (:type spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :axiom
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value nil
          :rainbow/transparency :opaque
          :rainbow/dependencies (term/constants type)
          :rainbow/provenance
          {:origin :native
           :producer :explicit-logical-profile
           :logical/profile profile
           :logical/principle (:principle spec)}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (reject! :logic-profile/principle-rejected
               "Logical principle was rejected"
               {:principle (:name spec) :result result}))
    [(:environment result) (:declaration result)]))

(defn activate
  "Adds the selected profile's principles to a checked environment.

  Returns the new environment plus the exact axiom IDs that a transaction must
  allow. Re-activation is content-idempotent."
  [checked-environment profile]
  (let [profile-spec (get profiles profile)]
    (when-not profile-spec
      (reject! :logic-profile/unknown-profile "Unknown logical profile"
               {:profile profile :available (set (keys profiles))}))
    (let [selected (->> principle-specs
                        (filter #(contains? (:profile/principles profile-spec)
                                            (:principle %)))
                        (sort-by (comp str :name)))]
      (loop [environment checked-environment
             remaining selected
             declarations []]
        (if-let [spec (first remaining)]
          (let [[next-environment declaration]
                (add-principle environment spec profile)]
            (recur next-environment (next remaining)
                   (conj declarations declaration)))
          {:status :activated
           :logical/profile profile
           :logical/principles (:profile/principles profile-spec)
           :logical/claim (:profile/claim profile-spec)
           :logical/axiom-ids (set (map :rainbow/id declarations))
           :logical/declarations declarations
           :environment environment
           :trusted-kernel-change :none})))))

(defn classify-axioms
  "Returns the named principles represented by an exact set of axiom IDs."
  [activation axiom-ids]
  (let [by-id (into {} (map (juxt :rainbow/id identity))
                    (:logical/declarations activation))
        unknown (remove by-id axiom-ids)]
    {:logical/profile (:logical/profile activation)
     :logical/principles
     (into (sorted-set)
           (keep #(get-in by-id [% :rainbow/provenance :logical/principle]))
           axiom-ids)
     :logical/unknown-axiom-ids (set unknown)
     :logical/within-profile?
     (and (empty? unknown)
          (every? (:logical/axiom-ids activation) axiom-ids))}))


;; ---- automated target classification ---------------------------------------
;;
;; Classification is pure OBSERVATION. It reads the axiom closure the kernel
;; already computes and the provenance the profile activation already recorded;
;; it never adds a declaration, so it cannot extend the trusted base. An axiom
;; that is not a declared principle is reported as unknown and BLOCKS any profile
;; claim -- silence would be exactly the silent extension the requirement forbids.

(def principle-by-name
  (into {} (map (juxt :name :principle)) principle-specs))

(defn principle-of
  "The named logical principle an axiom id represents in this environment, or
  :unknown when it is not a declared principle."
  [checked-environment axiom-id]
  (let [declaration (environment/declaration checked-environment axiom-id)]
    (or (get-in declaration [:rainbow/provenance :logical/principle])
        (some principle-by-name (:rainbow/aliases declaration))
        :unknown)))

(defn- covering-profiles [principles]
  (->> profiles
       (filter (fn [[_ spec]]
                 (every? (:profile/principles spec) principles)))
       (sort-by (fn [[name spec]]
                  [(count (:profile/principles spec)) (str name)]))))

(defn minimal-profile
  "The smallest declared profile whose principles cover the observed set."
  [principles]
  (or (ffirst (covering-profiles principles)) :unknown))

(defn classify-declaration
  "Classifies one checked declaration by the axioms in its dependency closure.

  Returns the exact axiom ids, the named principles they stand for, any axiom
  that is not a declared principle, and the smallest profile that covers the
  result. A declaration whose closure is empty is `:constructive`."
  [checked-environment id]
  (let [axiom-ids (set (kernel/axioms checked-environment id))
        named (into (sorted-set)
                    (map #(principle-of checked-environment %))
                    axiom-ids)
        unknown (into (sorted-set)
                      (filter #(= :unknown (principle-of checked-environment %)))
                      axiom-ids)
        principles (disj named :unknown)]
    {:logical/axiom-ids axiom-ids
     :logical/principles principles
     :logical/unknown-axiom-ids unknown
     :logical/profile (if (seq unknown) :unknown (minimal-profile principles))
     :logical/constructive? (empty? axiom-ids)}))

(defn within-profile?
  "True when a classification is admissible under a declared profile. An unknown
  axiom is never admissible, whatever the profile."
  [classification profile]
  (let [spec (get profiles profile)]
    (boolean (and spec
                  (empty? (:logical/unknown-axiom-ids classification))
                  (every? (:profile/principles spec)
                          (:logical/principles classification))))))

(defn classify-cohort
  "Classifies many targets at once and summarizes them for routing.

  `:logical/by-profile` counts targets per minimal profile, `:logical/outside`
  names the targets a requested profile cannot admit, and `:logical/unknown`
  names those resting on an axiom that is not a declared principle."
  ([checked-environment ids] (classify-cohort checked-environment ids nil))
  ([checked-environment ids requested]
   (let [classified (into (sorted-map)
                          (map (juxt identity
                                     #(classify-declaration checked-environment %)))
                          ids)]
     (cond-> {:logical/classified classified
              :logical/by-profile
              (into (sorted-map)
                    (frequencies (map :logical/profile (vals classified))))
              :logical/unknown
              (into (sorted-set)
                    (keep (fn [[id classification]]
                            (when (seq (:logical/unknown-axiom-ids classification))
                              id))
                          classified))}
       requested
       (assoc :logical/requested requested
              :logical/outside
              (into (sorted-set)
                    (keep (fn [[id classification]]
                            (when-not (within-profile? classification requested)
                              id))
                          classified)))))))
