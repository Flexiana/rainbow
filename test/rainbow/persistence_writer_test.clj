(ns rainbow.persistence-writer-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]))

(deftest environment-save-ignores-diagnostic-print-limits
  (let [env (corpus/build-environment)
        file (java.io.File/createTempFile "rainbow-env-" ".edn")]
    (try
      (binding [*print-length* 1 *print-level* 1 *print-readably* false]
        (is (= :saved (:status (persistence/save-environment! env file)))))
      (is (= :replayed (:status (persistence/load-environment file))))
      (finally (.delete file)))))

(defn- read-gzip [file]
  (with-open [input (java.util.zip.GZIPInputStream. (io/input-stream file))
              reader (java.io.PushbackReader. (io/reader input))]
    (edn/read reader)))

(deftest checkpoint-writers-preserve-complete-values
  (let [value {'exported/true {:description "a value with spaces" :nested [1 [2 [3]]]}}]
    (doseq [[label suffix writer reader]
            [[:plain ".edn" #'checkpoint/write-value! #(edn/read-string (slurp %))]
             [:gzip ".gz" #'checkpoint/write-value! read-gzip]
             [:frontier ".gz" frontier/write-checkpoint! read-gzip]]]
      (testing (name label)
        (let [file (java.io.File/createTempFile "rainbow-checkpoint-" suffix)]
          (try
            (binding [*print-length* 1 *print-level* 1 *print-readably* false
                      *print-namespace-maps* true]
              (writer file value))
            (is (= value (reader file)))
            (finally (.delete file))))))))

(deftest checkpoint-writers-accept-a-bare-filename
  (doseq [[label suffix writer reader]
          [[:plain ".edn" #'checkpoint/write-value! #(edn/read-string (slurp %))]
           [:gzip ".gz" #'checkpoint/write-value! read-gzip]
           [:frontier ".gz" frontier/write-checkpoint! read-gzip]]]
    (testing (name label)
      (let [file (io/file (str "rainbow-writer-test-" (java.util.UUID/randomUUID) suffix))]
        (try
          (is (= {:value [1 2 3]}
                 (do (writer file {:value [1 2 3]}) (reader file))))
          (finally (.delete file)))))))

(deftest re-aliased-inductive-blocks-survive-persistence
  (let [first-result (kernel/add-inductive-block (environment/empty-environment)
                                                 inductive/bool-spec)
        renamed (-> inductive/bool-spec
                    (assoc :block/alias 'persisted/Bool)
                    (assoc-in [:block/constructors 0 :constructor/alias] 'persisted/false)
                    (assoc-in [:block/constructors 1 :constructor/alias] 'persisted/true))
        second-result (kernel/add-inductive-block (:environment first-result) renamed)
        before (:environment second-result)
        artifact (persistence/environment-artifact before)
        replayed (persistence/replay-artifact artifact)]
    (is (= :accepted (:status first-result)))
    (is (= :accepted (:status second-result)))
    (is (= :replayed (:status replayed)) (pr-str (:error replayed)))
    (is (= (:rainbow.environment/aliases before)
           (:rainbow.environment/aliases (:environment replayed))))
    (is (= 2 (count (distinct (:rainbow.artifact/inductive-blocks artifact)))))
    (is (= artifact (persistence/environment-artifact (:environment replayed))))
    (is (= :rejected (:status (persistence/replay-artifact
                              (update-in artifact [:rainbow.artifact/entries 0 :entry/value]
                                         assoc :rainbow/id "sha256:forged")))))))
