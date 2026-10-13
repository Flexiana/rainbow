(ns rainbow.history.failure-memory
  "Cross-run failure-memory dogfood on a deliberately uninhabited implication."
  (:require [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.elaborate :as elaborate]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.storage :as storage]))

(def runs-path "artifacts/day2/runs.edn")

(def target
  (:term (elaborate/type-expression (first-tactic-program/forall '[A B] [:-> 'A 'B]))))

(defn stored-blocked-run []
  (first (filter #(= :blocked (:outcome %)) (storage/read-runs runs-path))))

(defn search-once [known-failures]
  (search/prove (:state (proof/start (direct-term-corpus/build-environment) target))
                {:states 1000 :depth 32 :wall-ms 10000
                 :known-failures known-failures}))

(defn report []
  (let [stored (stored-blocked-run)
        keys (search/failure-keys (:attempts stored))
        baseline (search-once #{})
        cached (search-once keys)
        cached-failures (search/failure-keys (:attempts cached))]
    {:status (if (and (= :blocked (:status baseline))
                      (= :blocked (:status cached))
                      (empty? cached-failures)
                      (pos? (get-in cached [:telemetry :failure-cache-hits] 0))
                      (seq (:remaining cached)))
               :passed :failed)
     :goal/hash (search/goal-hash (direct-term-corpus/build-environment)
                                  (proof/current-goal
                                   (:state (proof/start (direct-term-corpus/build-environment) target))))
     :known-failures (count keys)
     :baseline {:attempts (count (:attempts baseline))
                :failed-attempts (count (search/failure-keys (:attempts baseline)))}
     :cached {:attempts (count (:attempts cached))
              :failed-attempts (count cached-failures)
              :cache-hits (get-in cached [:telemetry :failure-cache-hits])
              :remaining (count (:remaining cached))}}))

(defn -main [& _]
  (println (pr-str (report))))
