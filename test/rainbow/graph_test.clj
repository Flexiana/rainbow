(ns rainbow.graph-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.test :refer :all]
            [rainbow.history.proof-graph :as proof-graph]
            [rainbow.environment :as environment]
            [rainbow.graph :as graph]
            [rainbow.foreign.lean :as lean]))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main"
         arguments))

(deftest checked-corpus-and-attempts-become-a-valid-graph
  (let [value (proof-graph/build-graph)
        validation (graph/validate value)]
    (is (= :valid (:status validation)))
    (is (= 197 (count (:graph/nodes value))))
    (is (= 275 (count (:graph/edges value))))
    (is (= 31 (count (:graph/aliases value))))
    (is (seq (graph/failed-goals value)))
    (is (every? seq (map #(graph/attempts-for value %)
                         (graph/failed-goals value))))))

(deftest aliases-do-not-change-semantic-graph-identity
  (let [value (proof-graph/build-graph)
        identity-id (graph/resolve-alias value 'logic/polymorphic-identity)
        declaration (get-in value [:graph/nodes identity-id :graph.node/declaration])
        with-alias (graph/add-declaration
                    value (update declaration :rainbow/aliases conj 'logic/another-id))]
    (is (= identity-id (graph/resolve-alias with-alias 'logic/another-id)))
    (is (= (graph/graph-id value) (graph/graph-id with-alias)))))

(deftest proof-diversity-shares-a-claim-and-dependencies-query-bidirectionally
  (let [value (proof-graph/build-graph)
        identity-id (graph/resolve-alias value 'logic/polymorphic-identity)
        reuse-id (graph/resolve-alias value 'graph/identity-reuse)
        identity (get-in value [:graph/nodes identity-id :graph.node/declaration])
        reuse (get-in value [:graph/nodes reuse-id :graph.node/declaration])]
    (is (= (graph/claim-id identity) (graph/claim-id reuse)))
    (is (not= (graph/proof-id identity) (graph/proof-id reuse)))
    (is (= #{identity-id} (graph/dependencies value reuse-id)))
    (is (contains? (graph/dependents value identity-id) reuse-id))))

(deftest graph-validation-rejects-content-tampering
  (let [value (proof-graph/build-graph)
        proof-node (first (filter #(= :proof (:graph.node/kind %))
                                  (vals (:graph/nodes value))))
        id (:graph.node/id proof-node)
        forged (assoc-in value [:graph/nodes id :graph.node/proof :proof/term]
                         [:bound 999])
        result (graph/validate forged)]
    (is (= :rejected (:status result)))
    (is (= :graph/node-id-mismatch (get-in result [:error :error/category])))))

(deftest foreign-node-validation-rejects-raw-content-tampering
  (let [fixture (lean/load-neutral "artifacts/day12/lean-neutral.edn")
        value (:graph (lean/ingest-foreign-graph fixture))
        node (first (filter #(= :foreign-declaration (:graph.node/kind %))
                            (vals (:graph/nodes value))))
        id (:graph.node/id node)
        forged (assoc-in value
                         [:graph/nodes id :graph.node/foreign-object
                          :foreign/raw-type]
                         [:forged])
        result (graph/validate forged)]
    (is (= :rejected (:status result)))
    (is (= :graph/node-id-mismatch (get-in result [:error :error/category])))))

(deftest graph-persists-and-replays-in-fresh-processes
  (let [path (.getAbsolutePath (java.io.File/createTempFile "rainbow-graph-" ".edn"))
        value (proof-graph/build-graph)
        saved (graph/save! value path)
        local (graph/load! path)
        replay (java-command "-m" "rainbow.history.proof-graph" "replay" path)
        fresh-reports (repeatedly 3 #(java-command "-m" "rainbow.history.proof-graph"))]
    (try
      (is (= :saved (:status saved)))
      (is (= :replayed (:status local)))
      (is (= (graph/graph-id value) (:graph/id local)))
      (is (zero? (:exit replay)) (:err replay))
      (is (every? #(zero? (:exit %)) fresh-reports))
      (is (= 1 (count (set (map :out fresh-reports)))))
      (finally (.delete (io/file path))))))
