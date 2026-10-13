(ns rainbow.history.mathlib-catalog-baseline
  "Authoritative proof-redacted Mathlib declaration and coverage baseline."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.foreign.mathlib :as mathlib]))

(def report-path "artifacts/day26/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")

(defn- top-counts [counts limit]
  (->> counts
       (sort-by (fn [[name count]] [(- count) (str name)]))
       (take limit)
       (mapv (fn [[name count]] {:name name :theorems count}))))

(defn report [catalog-path]
  (let [proof-report (mathlib-hidden-batch-1/report)
        mappings (get-in proof-report [:proofs :mappings])
        proved-names (set (map :foreign/name mappings))
        summary (mathlib/summarize catalog-path proved-names)
        passed? (and (= :passed (:status proof-report))
                     (= 5 (count proved-names))
                     (= 5 (:proved summary))
                     (> (:theorems summary) (:proved summary))
                     (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib
                  :version mathlib/pinned-version
                  :commit mathlib/pinned-commit
                  :scope :compiled-declarations-originating-in-mathlib-modules}
         :catalog {:id (:catalog/id summary)
                   :schema-version 2
                   :format :gzip-newline-delimited-edn
                   :proof-values :redacted
                   :statement-representation :lean-hash64-profile
                   :generated-artifact-committed? false}
         :inventory (select-keys summary
                                 [:declarations :declaration-occurrences
                                  :theorem-occurrences :theorems :public-theorems
                                  :private-theorems :kinds :modules :unsafe])
         :coverage {:independently-proved (:proved summary)
                    :theorem-declarations (:theorems summary)
                    :ratio (get-in summary [:coverage :ratio])
                    :percent (* 100 (get-in summary [:coverage :ratio]))
                    :proof-batch-report (:report/id proof-report)
                    :mappings mappings}
         :nativeization-baseline
         {:structurally-representable-theorems
          (:structural-fragment-theorems summary)
          :unsupported-binder-theorem-counts (:unsupported-binders summary)
          :unsupported-expression-theorem-counts (:unsupported-operators summary)
          :unsupported-feature-theorem-counts (:unsupported-features summary)
          :constant-resolution-measured? false
          :interpretation
          :syntax-shape-only-not-a-claim-that-foreign-constants-are-native}
         :curriculum-signals
         {:largest-theorem-modules
          (top-counts (:theorem-module-counts summary) 10)
          :smallest-unproved-structural-candidates
          (:candidate-theorems summary)
          :candidate-warning
          :foreign-constant-resolution-and-native-semantics-still-required}
         :method
         {:denominator :distinct-lean-theorem-names-from-mathlib-modules
          :imported-olean-occurrences-deduplicated? true
          :original-kinds-from-private-olean-parts? true
          :private-theorem-declarations-included? true
          :generated-theorems-silently-excluded? false
          :source-text-regex-used-as-denominator? false
          :lean-proof-bodies-visible-to-rainbow? false
          :declaration-identities :foreign-name-plus-lean-structural-fingerprint
          :per-statement-fingerprint-bits 64
          :catalog-wide-identity :sha256
          :full-statements :extracted-proof-redacted-per-bounded-stratum
          :streaming? true}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib-coverage/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-coverage/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report (or path default-catalog-path))))
    "replay" (let [result (load-report (or path report-path))]
                 (println (pr-str result))
                 (when-not (= :replayed (:status result)) (System/exit 1)))
    (let [value (report (or command default-catalog-path))]
      (println (pr-str value))
      (when-not (= :passed (:status value)) (System/exit 1)))))
