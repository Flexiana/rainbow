(ns rainbow.history.lean-hidden-body-inhabitation
  "Independent native inhabitation of hidden-body Lean claims."
  (:require [clojure.set :as set]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(defn hidden-claims []
  (let [{foreign-environment :environment objects :objects} (lean/build)]
    (mapv (fn [object]
            (let [declaration (environment/declaration
                               foreign-environment
                               (:foreign/native-declaration-id object))]
              {:foreign/name (:foreign/name object)
               :foreign/id (:foreign/native-declaration-id object)
               :claim/type (:rainbow/type declaration)
               :claim/universes (:rainbow/universes declaration)}))
          objects)))

(def proof-jobs
  [{:name 'native.reproved/polymorphic-identity
    :foreign/name "RainbowFixture.polymorphicIdentity" :plan :identity-assumption}
   {:name 'native.reproved/constant-function
    :foreign/name "RainbowFixture.constantFunction" :plan :constant-assumption}
   {:name 'native.reproved/apply-function
    :foreign/name "RainbowFixture.applyFunction" :plan :apply-function}
   {:name 'native.reproved/implication-identity
    :foreign/name "RainbowFixture.implicationIdentity" :plan :identity-assumption}
   {:name 'native.reproved/implication-transitivity
    :foreign/name "RainbowFixture.implicationTransitivity" :plan :transitivity-apply}
   {:name 'native.reproved/nat-identity
    :foreign/name "RainbowFixture.natIdentity" :plan :nat-identity}
   {:name 'native.reproved/nat-zero
    :foreign/name "RainbowFixture.natZero" :plan :nat-zero}
   {:name 'native.reproved/nat-successor
    :foreign/name "RainbowFixture.natSuccessor" :plan :nat-successor}
   {:name 'native.reproved/polymorphic-identity-exact
    :foreign/name "RainbowFixture.polymorphicIdentity" :plan :identity-exact}
   {:name 'native.reproved/implication-transitivity-exact
    :foreign/name "RainbowFixture.implicationTransitivity" :plan :transitivity-exact}])

(defn- run-step [result next-tactic]
  (if (contains? #{:ready :progress} (:status result))
    (tactic/run (:state result) next-tactic)
    result))

(defn- run-plan [environment claim plan]
  (let [started (proof/start environment (:claim/type claim)
                             {:universes (:claim/universes claim)})
        intros (fn [result count]
                 (reduce (fn [current _] (run-step current (tactic/intro)))
                         result (range count)))
        zero (term/constant (environment/resolve-id environment 'data/zero) [])
        successor (term/constant (environment/resolve-id environment 'data/succ) [])]
    (case plan
      :identity-assumption (run-step (intros started 2) (tactic/assumption))
      :constant-assumption (run-step (intros started 4) (tactic/assumption))
      :apply-function (-> started
                          (intros 4)
                          (run-step (tactic/apply [:bound 1]))
                          (run-step (tactic/assumption)))
      :transitivity-apply (-> started
                              (intros 6)
                              (run-step (tactic/apply [:bound 1]))
                              (run-step (tactic/apply [:bound 2]))
                              (run-step (tactic/assumption)))
      :nat-identity (run-step (intros started 1) (tactic/assumption))
      :nat-zero (run-step started (tactic/exact zero))
      :nat-successor (run-step (intros started 1)
                               (tactic/exact (term/application successor [:bound 0])))
      :identity-exact (run-step (intros started 2) (tactic/exact [:bound 0]))
      :transitivity-exact
      (run-step (intros started 6)
                (tactic/exact (term/application
                               [:bound 1]
                               (term/application [:bound 2] [:bound 0])))))))

(defn- register-proof [environment claim job]
  (let [result (run-plan environment claim (:plan job))]
    (when-not (= :proved (:status result))
      (throw (ex-info "Independent native proof failed" {:job job :result result})))
    (let [type (get-in result [:proof :proof/type])
          value (get-in result [:proof :proof/term])
          added (kernel/add-declaration
                 environment
                 {:rainbow/kind :theorem
                  :rainbow/aliases #{(:name job)}
                  :rainbow/universes (:claim/universes claim)
                  :rainbow/type type
                  :rainbow/value value
                  :rainbow/transparency :opaque
                  :rainbow/dependencies (into (term/constants type)
                                              (term/constants value))
                  :rainbow/provenance {:origin :native
                                       :producer :independent-reproof
                                       :foreign/name (:foreign/name claim)
                                       :foreign/proof-hidden? true}
                  :rainbow/schema-version 1})]
      (when-not (= :accepted (:status added))
        (throw (ex-info "Independent proof declaration rejected"
                        {:job job :result added})))
      {:environment (:environment added)
       :result result
       :declaration (:declaration added)
       :claim claim
       :job job})))

(defn build []
  (let [claims (hidden-claims)
        by-name (into {} (map (juxt :foreign/name identity)) claims)
        foreign-ids (set (map :foreign/id claims))]
    (reduce
     (fn [{:keys [environment results relationships]} job]
       (let [claim (get by-name (:foreign/name job))
             registered (register-proof environment claim job)
             declaration (:declaration registered)
             proof-term (get-in registered [:result :proof :proof/term])
             foreign-dependencies (set/intersection foreign-ids (term/constants proof-term))
             relationship
             {:native/id (:rainbow/id declaration)
              :foreign/id (:foreign/id claim)
              :foreign/name (:foreign/name claim)
              :relation :same-type
              :type-check (= (:claim/type claim) (:rainbow/type declaration))
              :foreign-proof-hidden? true
              :foreign-proof-dependencies foreign-dependencies}]
         {:environment (:environment registered)
          :results (conj results registered)
          :relationships (conj relationships relationship)}))
     {:environment (lean/base-environment) :results [] :relationships []}
     proof-jobs)))

(defn report []
  (let [{:keys [environment results relationships]} (build)]
    {:status :passed
     :proofs (count results)
     :distinct-claims (count (set (map #(get-in % [:claim :foreign/name]) results)))
     :relationships (count relationships)
     :all-types-checked? (every? :type-check relationships)
     :foreign-proof-dependencies (apply set/union
                                        (map :foreign-proof-dependencies relationships))
     :axioms (into {} (map (fn [{:keys [job]}]
                            [(:name job) (kernel/axioms environment (:name job))])
                          results))
     :declarations (count (:rainbow.environment/declarations environment))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (:environment (build)) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
