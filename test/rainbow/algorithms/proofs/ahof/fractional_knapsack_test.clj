(ns rainbow.algorithms.proofs.ahof.fractional-knapsack-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.fractional-knapsack :as fk]
            [rainbow.algorithms.reference.fractional-knapsack :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          fk/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fractional-knapsack-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (fk/definition-ids checked-environment)
        theorems (fk/theorem-ids checked-environment)]
    (is (= #{'fractional-knapsack/prefer?} (set (keys definitions))))
    (is (= #{'fractional-knapsack/prefers-higher-density
             'fractional-knapsack/preferred-has-higher-density
             'fractional-knapsack/rejects-lower-density}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-fractional-knapsack
  (is (true? (executable/prefer? 3 2)))
  (is (false? (executable/prefer? 2 5)))
  ;; capacity 50, items [60 10][100 20][120 30]: densities 6,5,4 -> 60+100+2/3*120=240
  (is (= 240 (executable/max-value 50 [[60 10] [100 20] [120 30]]))))
