(ns rainbow.algorithms.proofs.order-statistic-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.order-statistic :as order-statistic]
            [rainbow.algorithms.reference.order-statistic :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          order-statistic/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest order-statistic-count-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (order-statistic/definition-ids checked-environment)
        theorems (order-statistic/theorem-ids checked-environment)]
    (is (= #{'order-statistic/count-at-most} (set (keys definitions))))
    (is (= #{'order-statistic/cons-below-increments
             'order-statistic/cons-above-preserves
             'order-statistic/count-example
             'order-statistic/count-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-order-statistic-matches-the-count
  (is (= 2 (executable/count-at-most 5 [3 7 2])))
  (is (= 0 (executable/count-at-most 5 [])))
  (is (= 3 (executable/count-at-most 10 [3 7 2])))
  (is (= 1/3 (executable/empirical-cdf 2 [3 7 2])))
  (is (= 2 (executable/rank 5 [3 7 2]))))
