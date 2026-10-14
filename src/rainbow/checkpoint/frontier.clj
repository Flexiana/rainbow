(ns rainbow.checkpoint.frontier
  "Build and write a proving-frontier checkpoint (mappings, remaining targets, latest outcomes) from a build.
  (Checkpoint frontier bookkeeping.)"
  (:require [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.persistence :as persistence])
  (:import (java.util.zip GZIPOutputStream)))

(defn- result-outcome [result]
  {:status (:status result)
   :reason (:reason result)
   :states-created (get-in result [:telemetry :states-created])
   :max-depth (get-in result [:telemetry :max-depth])
   :wall-ms (get-in result [:telemetry :wall-ms])})

(defn checkpoint [build]
  (let [prior (:prior build)
        new-mappings (:new-mappings build)
        proved-names (set (map :foreign/name new-mappings))
        all-mappings (vec (concat (:mappings prior) new-mappings))
        remaining-targets (->> (:remaining-targets prior)
                               (remove #(contains? proved-names
                                                   (:foreign/name %)))
                               vec)
        remaining-names (set (map :foreign/name remaining-targets))
        candidate-outcomes
        (into {}
              (map (fn [evaluation]
                     [(get-in evaluation [:target :foreign/name])
                      (result-outcome (:result evaluation))]))
              (:evaluations build))
        latest-outcomes (-> (merge (:latest-outcomes prior) candidate-outcomes)
                            (select-keys remaining-names))
        base
        {:rainbow.checkpoint/kind :mathlib-proving-frontier
         :rainbow.checkpoint/schema-version 1
         :source (:source prior)
         :environment (persistence/environment-artifact (:environment build))
         :mappings all-mappings
         :remaining-targets remaining-targets
         :remaining-partitions
         (select-keys (:remaining-partitions prior) remaining-names)
         :latest-outcomes latest-outcomes}]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn write-checkpoint! [path value]
  (let [file (io/file (str path))
        serialized (binding [*print-namespace-maps* false
                             *print-length* nil *print-level* nil
                             *print-meta* false *print-dup* false *print-readably* true]
                     (str (pr-str value) "\n"))]
    (when-let [parent (.getParentFile file)] (.mkdirs parent))
    (with-open [output (GZIPOutputStream. (io/output-stream file))
                writer (io/writer output)]
      (.write writer serialized))))
