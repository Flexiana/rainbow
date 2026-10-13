(ns rainbow.algorithms.proofs.ahof.subset-sum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.subset-sum :as ss]
            [rainbow.algorithms.reference.subset-sum :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ss/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest subset-sum-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ss/definition-ids checked-environment)
        theorems (ss/theorem-ids checked-environment)]
    (is (= #{'subset-sum/reachable?} (set (keys definitions))))
    (is (= #{'subset-sum/include-branch-reachable
             'subset-sum/exclude-branch-reachable
             'subset-sum/both-fail-unreachable}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-subset-sum
  (is (true? (executable/reachable? true false)))
  (is (true? (executable/reachable? false true)))
  (is (false? (executable/reachable? false false)))
  ;; {3 34 4 12 5 2} has a subset summing to 9 (4+5) but not to 11
  (is (true? (executable/subset-sum? [3 34 4 12 5 2] 9)))
  (is (false? (executable/subset-sum? [3 34 4 12 5 2] 13))))
