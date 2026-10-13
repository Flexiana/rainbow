(ns rainbow.history.proof-graph
  "Day-3 graph dogfood over the persisted checked corpus and run history."
  (:require [rainbow.environment :as environment]
            [rainbow.graph :as graph]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.storage :as storage]
            [rainbow.term :as term]))

(def environment-path "artifacts/day2/environment.edn")
(def runs-path "artifacts/day2/runs.edn")

(defn build-environment []
  (let [environment-result (persistence/load-environment environment-path)]
    (when-not (= :replayed (:status environment-result))
      (throw (ex-info "Checked environment failed replay"
                      {:result environment-result})))
    (let [base (:environment environment-result)
          identity-id (environment/resolve-id base 'logic/polymorphic-identity)
          identity (environment/declaration base identity-id)
          result (kernel/add-declaration
                  base
                  {:rainbow/kind :theorem
                   :rainbow/aliases #{'graph/identity-reuse}
                   :rainbow/universes ['u]
                   :rainbow/type (:rainbow/type identity)
                   :rainbow/value (term/constant identity-id [[:param 'u]])
                   :rainbow/transparency :opaque
                   :rainbow/dependencies #{identity-id}
                   :rainbow/provenance {:origin :native :producer :day-3-dogfood}
                   :rainbow/schema-version 1})]
      (when-not (= :accepted (:status result))
        (throw (ex-info "Dependency dogfood proof failed" {:result result})))
      (:environment result))))

(defn build-graph []
  (-> (graph/empty-graph)
      (graph/add-environment (build-environment))
      (graph/add-runs (storage/read-runs runs-path))))

(defn report []
  (let [value (build-graph)
        validation (graph/validate value)
        failed (graph/failed-goals value)
        reuse-id (graph/resolve-alias value 'graph/identity-reuse)]
    {:status (if (= :valid (:status validation)) :passed :failed)
     :graph/id (:graph/id validation)
     :nodes (count (:graph/nodes value))
     :edges (count (:graph/edges value))
     :aliases (count (:graph/aliases value))
     :dependency-edges (count (graph/dependencies value reuse-id))
     :failed-goals (count failed)
     :failed-attempts (reduce + (map #(count (filter (fn [attempt]
                                                       (= :failure (:result attempt)))
                                                     (graph/attempts-for value %)))
                                     failed))}))

(defn -main [& [command path]]
  (case command
    "write" (println (pr-str (graph/save! (build-graph) path)))
    "replay" (let [result (graph/load! path)]
               (println (pr-str (dissoc result :graph)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
