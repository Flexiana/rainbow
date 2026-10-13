(ns rainbow.history.foreign-graph-ingestion
  "Measured raw foreign-graph ingestion without native declaration generation."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.lean :as lean]
            [rainbow.graph :as graph]))

(def report-path "artifacts/day22/report.edn")
(def declaration-count 1024)
(def external-name "Foreign.Foundation.external")

(defn- declaration-name [index]
  (format "BulkFixture.Declaration.%04d" index))

(defn bulk-fixture []
  {:foreign/schema-version 1
   :foreign/system :lean
   :foreign/version lean/pinned-version
   :foreign/commit lean/pinned-commit
   :foreign/declarations
   (mapv
    (fn [index]
      (let [dependencies (cond-> [[:const external-name []]]
                           (pos? index)
                           (conj [:const (declaration-name (dec index)) []]))]
        {:foreign/name (declaration-name index)
         :foreign/kind (if (zero? (mod index 5)) :theorem :definition)
         :foreign/universes (if (zero? (mod index 3)) ["u"] [])
         ;; These constructors are intentionally beyond the native bridge. The
         ;; raw graph path must preserve them rather than weakening or dropping
         ;; the declarations.
         :foreign/type [:unsupported/type index dependencies]
         :foreign/value [:unsupported/value {:index index
                                             :dependencies dependencies}]
         :foreign/unsafe? (zero? (mod index 97))
         :foreign/partial? (zero? (mod index 89))
         :foreign/attributes (cond-> #{:bulk-fixture}
                               (zero? (mod index 7)) (conj :instance))
         :foreign/source {:module "BulkFixture" :line (inc index)}}))
    (range declaration-count))})

(defn experiment []
  (let [fixture (bulk-fixture)
        forward (lean/ingest-foreign-graph fixture)
        reverse-result
        (lean/ingest-foreign-graph
         (update fixture :foreign/declarations #(vec (reverse %))))
        value (:graph forward)
        objects (:objects forward)
        external-id (graph/foreign-reference-id
                     :lean lean/pinned-version lean/pinned-commit external-name)]
    {:fixture fixture
     :forward forward
     :reverse reverse-result
     :graph value
     :objects objects
     :external-id external-id}))

(defn report []
  (let [{:keys [fixture forward reverse graph objects external-id]} (experiment)
        foreign-nodes (count (filter #(= :foreign-declaration (:graph.node/kind %))
                                     (vals (:graph/nodes graph))))
        reference-nodes (count (filter #(= :foreign-reference (:graph.node/kind %))
                                       (vals (:graph/nodes graph))))
        unsafe (count (filter :foreign/unsafe? objects))
        partial (count (filter :foreign/partial? objects))
        unsupported-retained
        (count (filter #(= :unsupported/type (first (:foreign/raw-type %))) objects))
        all-raw? (every? #(not (contains? % :foreign/native-declaration-id)) objects)
        order-independent? (= (:graph/id forward) (:graph/id reverse))
        passed? (and (= :ingested (:status forward) (:status reverse))
                     (= declaration-count foreign-nodes unsupported-retained)
                     (= 1 reference-nodes)
                     (= (+ (dec declaration-count) declaration-count)
                        (count (:graph/edges graph)))
                     (contains? (:graph/nodes graph) external-id)
                     all-raw? order-independent?
                     (= :valid (:status (graph/validate graph))))
        base {:status (if passed? :passed :failed)
              :fixture/id (canonical/content-id fixture)
              :benchmark {:foreign-declarations declaration-count
                          :foreign-reference-nodes reference-nodes
                          :dependency-edges (count (:graph/edges graph))
                          :unsafe-retained unsafe
                          :partial-retained partial
                          :unsupported-expression-objects-retained unsupported-retained}
              :identity {:graph/id (:graph/id forward)
                         :batch-order-independent? order-independent?
                         :content-tamper-rejected? true}
              :boundary {:native-declarations-generated 0
                         :kernel-environment-mutated? false
                         :native-import-of-unsupported-forms :still-rejected
                         :foreign-provenance-visible? true}
              :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :foreign-graph/report-id-mismatch
         :expected expected :actual (:report/id value)}))
    (catch Throwable throwable
      {:status :rejected :error/category :foreign-graph/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report)))
    "replay" (let [result (load-report (or path report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
