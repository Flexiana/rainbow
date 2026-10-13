(ns rainbow.algorithms.proofs.ahof.counting-sort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.counting-sort :as cs]
            [rainbow.algorithms.reference.counting-sort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          cs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest counting-sort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (cs/definition-ids checked-environment)
        theorems (cs/theorem-ids checked-environment)]
    (is (= #{'counting-sort/cumulative-counts} (set (keys definitions))))
    (is (= #{'counting-sort/offsets-example 'counting-sort/offsets-are-prefix-sum}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-counting-sort
  (is (= [2 3 6] (executable/cumulative-counts [2 1 3])))
  (is (= [0 0 1 2 2 2] (executable/counting-sort [2 0 1 2 0 2] 3)))
  (is (= [1 2 2 3 3 3] (executable/counting-sort [3 2 3 1 2 3] 4))))
