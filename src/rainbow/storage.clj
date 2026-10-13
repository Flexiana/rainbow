(ns rainbow.storage
  "Small append-only EDN run store for proof attempts and telemetry."
  (:require [clojure.edn :as edn]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]
            [rainbow.schemas :as schemas]))

(defn run-record [job-id result]
  (let [base {:rainbow/kind :proof-run
              :run/schema-version 1
              :job/id job-id
              :outcome (:status result)
              :proof/id (when-let [proof (:proof result)]
                          (canonical/content-id
                           (select-keys proof [:proof/term :proof/type :proof/environment-id])))
              :attempts (:attempts result)
              :telemetry (:telemetry result)}]
    (assoc base :run/id (canonical/content-id base))))

(defn append-run! [path job-id result]
  (let [record (run-record job-id result)]
    (spit path (str (pr-str record) "\n") :append true)
    {:status :stored :run/id (:run/id record) :path (str path)}))

(defn read-runs [path]
  (->> (string/split-lines (slurp path))
       (remove string/blank?)
       (mapv edn/read-string)))

(defn validate-run-record [record]
  (let [issues (schemas/explain-run-record record)]
    (if (empty? issues)
      {:status :valid :record record}
      {:status :rejected
       :error {:error/category :storage/run-schema-rejected
               :issues issues}})))

(defn read-runs-validated [path]
  (let [records (read-runs path)
        issues (vec
                (mapcat (fn [index record]
                          (map #(update % :path (fn [path] (into [index] path)))
                               (schemas/explain-run-record record)))
                        (range) records))]
    (if (empty? issues)
      {:status :valid :records records}
      {:status :rejected
       :error {:error/category :storage/runs-schema-rejected
               :issues issues}})))
