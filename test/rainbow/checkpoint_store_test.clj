(ns rainbow.checkpoint-store-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.checkpoint.store :as store]))

(def ^:private checked-env (delay (corpus/build-environment)))

(defn- with-checkpoints [f]
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory
                     "rainbow-store-" (make-array java.nio.file.attribute.FileAttribute 0)))
        ;; Use the production discovery filename in separate directories.
        files (mapv #(io/file dir (str %) "checkpoint.edn.gz") [1 2])
        store-file (io/file dir "store.edn.gz")
        original-file-seq file-seq
        values (mapv (fn [n]
                       (frontier/checkpoint
                        {:environment @checked-env
                         :prior {:source {:version mathlib/pinned-version :commit mathlib/pinned-commit}
                                 :remaining-targets [{:foreign/name (symbol "fixture" (str "target" n))}]}}))
                     [1 2])]
    (try
      (doseq [[file value] (map vector files values)] (#'store/write-gz! file value))
      (with-redefs [store/store-path (str store-file)
                    file-seq (fn [_] files)]
        (reset! @#'store/cache nil)
        (f files values store-file))
      (finally
        (reset! @#'store/cache nil)
        (doseq [file (reverse (original-file-seq dir))] (.delete file))))))

(deftest interrupted-packing-keeps-all-checkpoints-readable
  (with-checkpoints
    (fn [files values _]
      (let [write #'store/write-gz!
            original @write]
        (with-redefs-fn {write (fn [path value]
                                (if (= (str path) (str (second files)))
                                  (throw (java.io.IOException. "simulated interrupted packing"))
                                  (original path value)))}
          #(is (thrown? java.io.IOException (store/pack-all!))))
        (doseq [[file value] (map vector files values)]
          (let [expanded (store/expand (#'store/read-gz file))]
            (is (= value expanded))
            (is (= :replayed (:status (checkpoint/replay-checkpoint expanded))))))
        (is (= 2 (:checkpoints (store/pack-all!))))
        (is (zero? (:packed-now (store/pack-all!))))))))

(deftest failed-gzip-serialization-leaves-existing-file-intact
  (with-checkpoints
    (fn [files values _]
      (let [file (first files)]
        (with-redefs [pr-str (fn [& _] (throw (ex-info "serialization failed" {})))]
          (is (thrown? clojure.lang.ExceptionInfo (#'store/write-gz! file {:new :value}))))
        (is (= (first values) (#'store/read-gz file)))))))

(deftest failed-gzip-stream-write-preserves-the-old-file
  (with-checkpoints
    (fn [files values _]
      (let [file (first files)
            make-writer io/writer]
        (with-redefs [io/writer
                      (fn [& args]
                        (let [delegate (apply make-writer args)]
                          (proxy [java.io.Writer] []
                            (write
                              ([value]
                               (.write delegate (subs (str value) 0 2))
                               (throw (java.io.IOException. "simulated partial write")))
                              ([buffer offset length]
                               (.write delegate buffer offset (min 2 length))
                               (throw (java.io.IOException. "simulated partial write"))))
                            (flush [] (.flush delegate))
                            (close [] (.close delegate)))))]
          (is (thrown? java.io.IOException (#'store/write-gz! file {:new :value}))))
        (is (= (first values) (#'store/read-gz file)))
        (is (= #{"checkpoint.edn.gz"}
               (set (map #(.getName %) (.listFiles (.getParentFile file))))))))))

(deftest packing-ignores-diagnostic-print-settings
  (with-checkpoints
    (fn [files values _]
      (binding [*print-namespace-maps* true *print-length* 1 *print-level* 1
                *print-meta* true *print-dup* true *print-readably* false]
        (is (= 2 (:packed-now (store/pack-all!)))))
      (doseq [[file value] (map vector files values)]
        (is (= value (store/expand (#'store/read-gz file))))))))

(deftest altered-store-entries-still-fail-checkpoint-validation
  (with-checkpoints
    (fn [files _ store-file]
      (store/pack-all!)
      (let [packed (#'store/read-gz (first files))
            ref (get-in packed [:environment :rainbow.artifact/declarations 0 :rainbow.store/ref])
            entries (#'store/read-gz store-file)]
        (#'store/write-gz! store-file (update entries ref assoc :tampered true))
        (reset! @#'store/cache nil)
        (let [result (checkpoint/replay-checkpoint (store/expand packed))]
          (is (= :rejected (:status result)))
          (is (= :day54/checkpoint-id-mismatch (:error/category result))))))))
