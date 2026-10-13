(ns rainbow.algorithms.proofs.ahof.knapsack-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.knapsack :as knapsack]
            [rainbow.algorithms.reference.knapsack :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          knapsack/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest knapsack-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (knapsack/definition-ids checked-environment)
        theorems (knapsack/theorem-ids checked-environment)]
    (is (= #{'knapsack/cell} (set (keys definitions))))
    (is (= #{'knapsack/takes-when-better 'knapsack/leaves-when-better
             'knapsack/dominates-take 'knapsack/dominates-leave}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-knapsack
  (is (= 7 (executable/cell 5 7)))
  (is (= 8 (executable/cell 8 3)))
  ;; capacity 5, items [2 3][3 4][4 5][5 6]: best is [2 3]+[3 4] = 7
  (is (= 7 (executable/knapsack 5 [[2 3] [3 4] [4 5] [5 6]]))))
