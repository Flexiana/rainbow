(ns rainbow.accounting-reconciliation-test
  "Every count any stored report ever published must satisfy the single
  definition in rainbow.accounting. This is the guard against the numbers
  drifting apart again: it reads the artifacts, not the code that wrote them."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [rainbow.accounting :as accounting]))

(defn- stored-reports []
  (->> (file-seq (io/file "artifacts"))
       (filter #(= "report.edn" (.getName ^java.io.File %)))
       (sort-by #(.getPath ^java.io.File %))
       (keep (fn [file]
               (let [report (try (edn/read-string (slurp file))
                                 (catch Throwable _ nil))]
                 (when (seq (get-in report [:proofs :mappings]))
                   [(.getPath ^java.io.File file) (:proofs report)]))))))

(deftest every-stored-report-satisfies-the-single-accounting-definition
  (let [reports (stored-reports)]
    (is (< 25 (count reports))
        "the reconciliation must actually cover the corpus")
    (doseq [[path proofs] reports]
      (testing path
        (let [mappings (:mappings proofs)
              ;; a report that reused an existing abstraction, or created a
              ;; proof object outside its mappings, says so in its own fields
              reused (or (:native-abstractions-reused proofs) 0)
              additional (or (:invented-generalized-lemmas proofs) 0)
              account (accounting/mapping-account mappings)
              expected (+ (- (:accounting/distinct-proof-objects account) reused)
                          additional)]
          (when (contains? proofs :new-foreign-mappings)
            (is (= (:new-foreign-mappings proofs)
                   (:accounting/foreign-mappings account))))
          (when (contains? proofs :foreign-declarations)
            (is (= (:foreign-declarations proofs)
                   (:accounting/foreign-mappings account))))
          (when (contains? proofs :new-axiom-profiles)
            (is (= (:new-axiom-profiles proofs)
                   (:accounting/axiom-profiles account))))
          (when (contains? proofs :new-semantic-proof-objects)
            (is (= (:new-semantic-proof-objects proofs) expected))))))))

(deftest reuse-and-invention-are-modelled-not-special-cased
  (let [mappings [{:foreign/name "A" :proof/id "sha256:one"}
                  {:foreign/name "B" :proof/id "sha256:two"}]]
    (testing "a mapping onto an existing declaration creates nothing new"
      (is (= 0 (accounting/new-proof-objects
                [{:foreign/name "A" :proof/id "sha256:one"}]
                {:reused #{"sha256:one"}}))))
    (testing "a proof object outside the mappings still counts"
      (is (= 3 (accounting/new-proof-objects
                mappings {:additional #{"sha256:invented"}}))))
    (testing "aliased mappings onto one declaration count once"
      (is (= 1 (accounting/new-proof-objects
                [{:foreign/name "A" :proof/id "sha256:one"}
                 {:foreign/name "A-prime" :proof/id "sha256:one"}]))))
    (testing "older reports keyed the id as :native/id"
      (is (= 1 (accounting/new-proof-objects
                [{:foreign/name "A" :native/id "sha256:one"}]))))))
