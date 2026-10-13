(ns rainbow.foreign-graph-test
  (:require [clojure.test :refer :all]
            [rainbow.history.foreign-graph-ingestion :as foreign-graph-ingestion]))

(def live-report (delay (foreign-graph-ingestion/report)))

(deftest bulk-foreign-graph-is-content-addressed-and-order-independent
  (let [report @live-report]
    (is (= :passed (:status report)))
    (is (= 1024 (get-in report [:benchmark :foreign-declarations])))
    (is (= 1 (get-in report [:benchmark :foreign-reference-nodes])))
    (is (= 2047 (get-in report [:benchmark :dependency-edges])))
    (is (= 1024 (get-in report
                        [:benchmark :unsupported-expression-objects-retained])))
    (is (true? (get-in report [:identity :batch-order-independent?])))
    (is (true? (get-in report [:identity :content-tamper-rejected?])))))

(deftest raw-ingestion-does-not-claim-native-or-kernel-status
  (let [boundary (:boundary @live-report)]
    (is (zero? (:native-declarations-generated boundary)))
    (is (false? (:kernel-environment-mutated? boundary)))
    (is (= :still-rejected (:native-import-of-unsupported-forms boundary)))
    (is (true? (:foreign-provenance-visible? boundary)))
    (is (= :none (:trusted-base-change @live-report)))))
