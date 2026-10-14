(ns rainbow.checkpoint.store
  "Content-addressed storage for the declarations inside checkpoints.

  A checkpoint is a whole checked environment, so successive checkpoints repeat
  almost every declaration of the one before: measured 2026-10-12, 256
  checkpoints held 525,504 declaration copies of 2,634 distinct declarations.
  Packing stores each declaration once, in `store-path`, and leaves a reference
  `{:rainbow.store/ref \"sha256:...\"}` in its place.

  Reading is unchanged for every caller: `expand` puts each declaration back
  before anything checks the value, so the checkpoint's own content id and the
  kernel replay see exactly the value that was recorded. The store is not
  trusted. A missing or altered entry yields a value whose content id does not
  match, and the checkpoint is rejected as it would be for any other tampering."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io])
  (:import (java.io PushbackReader)
           (java.nio.file Files CopyOption StandardCopyOption)
           (java.nio.file.attribute FileAttribute)
           (java.security MessageDigest)
           (java.util.zip GZIPInputStream GZIPOutputStream)))

(def store-path "artifacts/store/declarations.edn.gz")

(defn- read-gz [path]
  (with-open [input (GZIPInputStream. (io/input-stream (str path)) 65536)
              reader (PushbackReader. (io/reader input))]
    (edn/read reader)))

(defn- edn-string [value]
  (binding [*print-namespace-maps* false
            *print-length* nil *print-level* nil
            *print-meta* false *print-dup* false *print-readably* true]
    (pr-str value)))

(defn- write-gz! [path value]
  (let [serialized (str (edn-string value) "\n")
        file (.getAbsoluteFile (io/file (str path)))
        parent (.getParentFile file)]
    (.mkdirs parent)
    (let [temporary (Files/createTempFile (.toPath parent) ".rainbow-store-" ".tmp"
                                          (make-array FileAttribute 0))]
      (try
        (with-open [output (GZIPOutputStream. (io/output-stream (.toFile temporary)) 65536)
                    writer (io/writer output)]
          (.write writer serialized))
        ;; Fail safely if atomic replacement is unsupported; never truncate the old file.
        (Files/move temporary (.toPath file)
                    (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE
                                            StandardCopyOption/REPLACE_EXISTING]))
        (finally (Files/deleteIfExists temporary))))))

(def ^:private cache (atom nil))

(defn- store
  "The store map (ref -> declaration), read once per file version."
  []
  (let [file (io/file store-path)
        stamp (.lastModified file)]
    (if (= stamp (first @cache))
      (second @cache)
      (let [value (if (.exists file) (read-gz file) {})]
        (reset! cache [stamp value])
        value))))

(defn- reference? [x]
  (and (map? x) (= 1 (count x)) (contains? x :rainbow.store/ref)))

(defn- resolve-reference [entries x]
  (if (reference? x)
    (or (get entries (:rainbow.store/ref x))
        (throw (ex-info "checkpoint refers to a declaration the store does not hold"
                        {:rainbow.store/ref (:rainbow.store/ref x) :store store-path})))
    x))

(defn- map-artifact
  "Applies f to every stored element of a checked-environment artifact."
  [artifact f]
  (cond-> artifact
    (:rainbow.artifact/declarations artifact)
    (update :rainbow.artifact/declarations #(mapv f %))
    (:rainbow.artifact/inductive-blocks artifact)
    (update :rainbow.artifact/inductive-blocks #(mapv f %))
    (:rainbow.artifact/entries artifact)
    (update :rainbow.artifact/entries #(mapv (fn [entry] (update entry :entry/value f)) %))))

(def ^:private top-level-vectors
  "Checkpoint keys whose vector elements repeat across checkpoints (the Mathlib frontier)."
  [:remaining-targets :mappings])

(defn- map-checkpoint
  "Applies f to every stored element of a checkpoint value: the environment
  artifact's declarations and blocks, and the elements of `top-level-vectors`."
  [value f]
  (reduce (fn [v k] (if (vector? (get v k)) (update v k #(mapv f %)) v))
          (update value :environment map-artifact f)
          top-level-vectors))

(defn- elements [value]
  (let [artifact (:environment value)]
    (concat (:rainbow.artifact/declarations artifact)
            (:rainbow.artifact/inductive-blocks artifact)
            (map :entry/value (:rainbow.artifact/entries artifact))
            (mapcat #(when (vector? (get value %)) (get value %)) top-level-vectors))))

(defn- packed? [value]
  (some reference? (elements value)))

(defn expand
  "A checkpoint value with every stored declaration put back. Values that were
  never packed are returned unchanged."
  [value]
  (if (and (map? value) (map? (:environment value)) (packed? value))
    (let [entries (store)]
      (map-checkpoint value #(resolve-reference entries %)))
    value))

;; ---------------------------------------------------------------- packing

(defn- sha256 [^String s]
  (let [digest (.digest (MessageDigest/getInstance "SHA-256") (.getBytes s "UTF-8"))]
    (str "sha256:" (apply str (map #(format "%02x" (bit-and 0xff %)) digest)))))

(defn- pack-value
  "[packed-value {ref element}] for one checkpoint value."
  [value]
  (let [found (volatile! {})
        packed (map-checkpoint value
                       (fn [element]
                         (let [ref (sha256 (edn-string element))]
                           (vswap! found assoc ref element)
                           {:rainbow.store/ref ref})))]
    [packed @found]))

(defn- references [value]
  (into #{} (comp (filter reference?) (map :rainbow.store/ref)) (elements value)))

(defn pack-all!
  "Packs every artifacts/**/checkpoint.edn.gz under the working directory in
  place and writes the store with exactly the declarations they reference.
  A file that is already packed is left as it is and only contributes its
  references; each newly packed file is checked to expand back to the value it
  replaced before it is written. The store is published before new references;
  interrupted writes leave complete, expandable checkpoints. Idempotent."
  []
  (let [files (->> (file-seq (io/file "artifacts"))
                   (filter #(= "checkpoint.edn.gz" (.getName ^java.io.File %)))
                   (sort-by str))
        old (store)
        entries (volatile! {})
        pending (volatile! [])]
    (doseq [f files]
      (let [value (read-gz f)]
        (if (every? reference? (elements value))   ; fully packed: only collect its references
          (doseq [ref (references value)]
            (vswap! entries assoc ref
                    (or (get old ref)
                        (throw (ex-info "packed checkpoint refers to a missing store entry"
                                        {:file (str f) :rainbow.store/ref ref})))))
          (let [value (expand value)               ; partly packed (an older layout): restore, then pack whole
                [packed found] (pack-value value)]
            (when-not (= value (map-checkpoint packed #(resolve-reference found %)))
              (throw (ex-info "packing does not round-trip" {:file (str f)})))
            (vswap! entries merge found)
            (vswap! pending conj [f packed])))))
    ;; Retain old references until every checkpoint has been replaced. A failed
    ;; replacement can then be retried with either the old or new checkpoint.
    (write-gz! store-path (merge old @entries))
    (reset! cache nil)
    (doseq [[file packed] @pending] (write-gz! file packed))
    (write-gz! store-path @entries)
    (reset! cache nil)
    {:checkpoints (count files) :packed-now (count @pending) :distinct-declarations (count @entries)}))

(defn -main [& _]
  (println (pr-str (pack-all!)))
  (shutdown-agents))
