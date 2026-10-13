(ns rainbow.session
  "Validated persistence and cheap immutable checkpoints for proof sessions."
  (:require [clojure.edn :as edn]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.term :as term]))

(def schema-version 1)

(defn checkpoint [state label]
  {:rainbow/kind :proof-checkpoint
   :checkpoint/schema-version schema-version
   :checkpoint/label label
   :checkpoint/session-id (:proof/session-id state)
   :checkpoint/state state})

(defn restore [checkpoint]
  (:checkpoint/state checkpoint))

(defn- partial-term? [value]
  (cond
    (proof/hole? value) (string? (second value))
    (not (vector? value)) false
    :else
    (case (first value)
      (:sort :bound :const) (term/term? value)
      :app (and (= 3 (count value))
                (partial-term? (second value))
                (partial-term? (nth value 2)))
      (:lam :pi) (and (= 4 (count value))
                      (term/term? (second value))
                      (partial-term? (nth value 2))
                      (contains? #{:explicit :implicit} (nth value 3)))
      :let (and (= 4 (count value))
                (term/term? (second value))
                (partial-term? (nth value 2))
                (partial-term? (nth value 3)))
      false)))

(defn- hole-ids [value]
  (cond
    (proof/hole? value) [(second value)]
    (vector? value) (mapcat hole-ids (rest value))
    :else []))

(defn- goal-well-formed? [environment universes goal]
  (let [context (:goal/context goal)
        target (:goal/target goal)]
    (and (string? (:goal/id goal))
         (vector? context)
         (every? #(and (symbol? (:goal/name %))
                       (term/term? (:goal/type %))
                       (contains? #{:explicit :implicit} (:goal/mode %)))
                 context)
         (term/term? target)
         (= :checked
            (:status
             (kernel/infer environment
                           (proof/close-over-context context target term/pi-term)
                           universes))))))

(defn validate-state [environment state]
  (let [goals (:proof/goals state)
        goal-ids (mapv :goal/id goals)
        holes (vec (hole-ids (:proof/partial-term state)))
        universes (:proof/universes state)
        expected-session-id (proof/session-id environment
                                              (:proof/root-goal state)
                                              (:proof/root-context state)
                                              universes)]
    (cond
      (not= :proof-state (:rainbow/kind state))
      {:status :rejected :error {:error/category :session/not-proof-state}}

      (not= 1 (:proof/schema-version state))
      {:status :rejected :error {:error/category :session/state-schema}}

      (not= expected-session-id (:proof/session-id state))
      {:status :rejected :error {:error/category :session/identity-mismatch}}

      (not (partial-term? (:proof/partial-term state)))
      {:status :rejected :error {:error/category :session/malformed-partial-term}}

      (not= (frequencies goal-ids) (frequencies holes))
      {:status :rejected
       :error {:error/category :session/hole-goal-mismatch
               :goals goal-ids :holes holes}}

      (not= (count goal-ids) (count (distinct goal-ids)))
      {:status :rejected :error {:error/category :session/duplicate-goal-id}}

      (not-every? #(goal-well-formed? environment universes %) goals)
      {:status :rejected :error {:error/category :session/invalid-goal}}

      :else {:status :valid :state (assoc state :proof/environment environment)})))

(defn artifact [state]
  {:rainbow.session/schema-version schema-version
   :rainbow.session/environment (persistence/environment-artifact
                                 (:proof/environment state))
   :rainbow.session/state (dissoc state :proof/environment)})

(defn save! [state path]
  (let [value (artifact state)]
    (spit path (str (pr-str value) "\n"))
    {:status :saved
     :path (str path)
     :session-id (:proof/session-id state)
     :goals (count (:proof/goals state))}))

(defn replay-artifact [value]
  (if-not (= schema-version (:rainbow.session/schema-version value))
    {:status :rejected :error {:error/category :session/artifact-schema}}
    (let [environment-result (persistence/replay-artifact
                              (:rainbow.session/environment value))]
      (if-not (= :replayed (:status environment-result))
        {:status :rejected
         :error {:error/category :session/environment-rejected
                 :cause environment-result}}
        (validate-state (:environment environment-result)
                        (:rainbow.session/state value))))))

(defn load! [path]
  (try
    (replay-artifact (edn/read-string (slurp path)))
    (catch Exception exception
      {:status :rejected
       :error {:error/category :session/malformed-artifact
               :class (str (class exception))}
       :message (.getMessage exception)})))
