(ns rainbow.operations-research-curriculum-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [rainbow.canonical :as canonical]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.foreign.mathlib :as mathlib]))

(def recorded-curriculum
  (delay (edn/read-string (slurp or40/curriculum-path))))

(deftest recorded-curriculum-is-pinned-redacted-and-content-addressed
  (let [curriculum @recorded-curriculum
        targets (:or.curriculum/targets curriculum)
        names (mapv :foreign/name targets)]
    (is (= (:or.curriculum/id curriculum)
           (canonical/content-id (dissoc curriculum :or.curriculum/id))))
    (is (= {:start "2026-08-18" :days 40 :conference "2026-09-27"}
           (:or.curriculum/window curriculum)))
    (is (= mathlib/pinned-version
           (get-in curriculum [:or.curriculum/source :foreign/version])))
    (is (= mathlib/pinned-commit
           (get-in curriculum [:or.curriculum/source :foreign/commit])))
    (is (= :redacted
           (get-in curriculum [:or.curriculum/source :proof-values])))
    (is (= 5000 (count targets) (count (distinct names))))
    (is (every? #(not (contains? % :foreign/value)) targets))
    (is (pos? (get-in curriculum [:or.curriculum/selection
                                  :structural-fragment-ready])))
    (is (pos? (get-in curriculum [:or.curriculum/selection
                                  :representation-work-required])))
    (is (= #{:common-foundations :bellman-operators :mcmc
             :bird-flock-optimization :conference-integration}
           (set (map :or/phase targets))))))

(deftest prerequisite-order-and-held-out-boundaries-are-explicit
  (let [curriculum @recorded-curriculum
        graph (:or.curriculum/prerequisite-graph curriculum)
        counts (frequencies (map :study/partition
                                 (:or.curriculum/targets curriculum)))]
    (is (= [] (get graph :common-foundations)))
    (is (= [:common-foundations] (get graph :bellman-operators)))
    (is (= [:common-foundations] (get graph :mcmc)))
    (is (= [:common-foundations] (get graph :bird-flock-optimization)))
    (is (= [:bellman-operators :mcmc :bird-flock-optimization]
           (get graph :conference-integration)))
    (is (= {:development 4000 :held-out 500 :transfer 500} counts))))

(deftest baseline-report-does-not-confuse-plans-with-proofs
  (let [report (edn/read-string (slurp or40/report-path))]
    (is (= :passed (:status report)))
    (is (= (:report/id report)
           (canonical/content-id (dissoc report :report/id))))
    (is (= 1174 (get-in report [:baseline :all-mathlib-exact-mappings])))
    (is (= 11 (get-in report [:first-foundation-cluster :native-theorems])))
    (is (= false (get-in report [:claim-boundaries
                                 :topic-selection-is-proof-credit?])))
    (is (= false (get-in report [:claim-boundaries
                                 :bellman-mcmc-and-flock-demos-complete?])))
    (is (= :replayed (:status (or40/load-report or40/report-path))))))

(deftest next-batch-is-ordered-unmapped-and-readiness-gated
  (let [curriculum
        {:or.curriculum/targets
         [{:foreign/name "mapped" :or/phase :common-foundations
           :rainbow/structural-fragment? true}
          {:foreign/name "representation" :or/phase :common-foundations
           :rainbow/structural-fragment? false}
          {:foreign/name "first" :or/phase :common-foundations
           :rainbow/structural-fragment? true}
          {:foreign/name "second" :or/phase :common-foundations
           :rainbow/structural-fragment? true}
          {:foreign/name "other" :or/phase :mcmc
           :rainbow/structural-fragment? true}]}
        mappings [{:foreign/name "mapped"}]]
    (is (= ["first" "second"]
           (mapv :foreign/name
                 (or40/next-proof-batch
                  curriculum mappings {:target-count 2}))))
    (is (= ["representation" "first"]
           (mapv :foreign/name
                 (or40/next-proof-batch
                  curriculum mappings {:target-count 2
                                       :structural-only? false}))))))
