(ns rainbow.checkpoint
  "Kernel-replayable checkpoints of a checked environment: read, write, replay and cached load. Loading always
  re-enters the kernel. (Error categories keep their original :day54/... keywords.)"
  (:require [rainbow.checkpoint.store :as store]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.persistence :as persistence])
  (:import (java.io PushbackReader)
           (java.util.zip GZIPInputStream GZIPOutputStream)))

(def checkpoint-path "artifacts/day54/checkpoint.edn.gz")

(defn replay-checkpoint [value]
  (let [expected (canonical/content-id
                  (dissoc value :rainbow.checkpoint/id))
        names (mapv :foreign/name (:remaining-targets value))
        mapped (set (map :foreign/name (:mappings value)))]
    (cond
      (not= 1 (:rainbow.checkpoint/schema-version value))
      {:status :rejected :error/category :day54/unsupported-schema}

      (not= expected (:rainbow.checkpoint/id value))
      {:status :rejected :error/category :day54/checkpoint-id-mismatch}

      (not= mathlib/pinned-version (get-in value [:source :version]))
      {:status :rejected :error/category :day54/version-mismatch}

      (not= mathlib/pinned-commit (get-in value [:source :commit]))
      {:status :rejected :error/category :day54/commit-mismatch}

      (not= (count names) (count (set names)))
      {:status :rejected :error/category :day54/duplicate-targets}

      (some mapped names)
      {:status :rejected :error/category :day54/mapped-target-remains}

      :else
      (let [replay (persistence/replay-artifact (:environment value))]
        (if (= :replayed (:status replay))
          (cond-> {:status :replayed
                   :checkpoint/id expected
                   :source (:source value)
                   :environment (:environment replay)
                   :environment/id (:environment-id replay)
                   :names/id (:names-id replay)
                   :mappings (:mappings value)
                   :remaining-targets (:remaining-targets value)
                   :remaining-partitions (:remaining-partitions value)
                   :latest-outcomes (:latest-outcomes value)}
            ;; mappings withdrawn by a migration (1.4.2): kept visible, carried into every later checkpoint
            (:retracted-mappings value) (assoc :retracted-mappings (:retracted-mappings value)))
          {:status :rejected :error/category :day54/environment-rejected
           :cause replay})))))

(defn- read-value [path]
  (if (.endsWith (str path) ".gz")
    (with-open [input (GZIPInputStream. (io/input-stream path))
                reader (PushbackReader. (io/reader input))]
      (store/expand (edn/read reader)))
    (store/expand (edn/read-string (slurp path)))))

(defn- write-value! [path value]
  (let [file (io/file (str path))
        serialized (binding [*print-namespace-maps* false
                             *print-length* nil *print-level* nil
                             *print-meta* false *print-dup* false *print-readably* true]
                     (str (pr-str value) "\n"))]
    (when-let [parent (.getParentFile file)] (.mkdirs parent))
    (if (.endsWith (str path) ".gz")
      (with-open [output (GZIPOutputStream. (io/output-stream file))
                  writer (io/writer output)]
        (.write writer serialized))
      (spit file serialized))))

(def ^:private replay-cache (atom {}))

(def checkpoint-migrations-paths
  "Records of releases that rewrote stored checkpoints, each mapping a checkpoint id to the id it was
  rewritten to."
  ["artifacts/migrations/1.4.2-checkpoint-ids.edn" "artifacts/migrations/1.4.3-checkpoint-ids.edn"])

(def ^:private migrated-checkpoint-ids
  (delay (into {} (map #(:migration/checkpoint-ids (edn/read-string (slurp %)))) checkpoint-migrations-paths)))

(defn same-input-checkpoint?
  "Whether a precommitted input checkpoint id names the checkpoint with id `actual`: it is that id, or a
  recorded checkpoint migration rewrote the precommitted checkpoint, possibly in several steps, into it.
  A precommitment is never edited after the fact; the migration record says what happened to its input."
  [precommitted actual]
  (loop [id precommitted seen #{}]
    (cond (= id actual) true
          (or (nil? id) (seen id)) false
          :else (recur (get @migrated-checkpoint-ids id) (conj seen id)))))

(defn load-checkpoint [path]
  (let [key [(str path)
             (try (.lastModified (io/file (str path))) (catch Throwable _ 0))]]
    (or (get @replay-cache key)
        (let [result
              (try
                (replay-checkpoint (read-value path))
                (catch Throwable throwable
                  {:status :rejected
                   :error/category :day54/checkpoint-read-failed
                   :message (.getMessage throwable)}))]
          ;; A rejection can be transient (I/O or a smaller reduction budget).
          ;; Only completed successful replays are reusable.
          (when (= :replayed (:status result))
            (swap! replay-cache assoc key result))
          result))))
