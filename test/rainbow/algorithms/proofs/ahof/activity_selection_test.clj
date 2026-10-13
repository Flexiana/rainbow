(ns rainbow.algorithms.proofs.ahof.activity-selection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.activity-selection :as act]
            [rainbow.algorithms.reference.activity-selection :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          act/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest activity-selection-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (act/definition-ids checked-environment)
        theorems (act/theorem-ids checked-environment)]
    (is (= #{'activity-selection/compatible?} (set (keys definitions))))
    (is (= #{'activity-selection/admits-compatible-activity
             'activity-selection/admitted-does-not-overlap
             'activity-selection/rejects-overlapping-activity}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-activity-selection
  (is (true? (executable/compatible? 5 3)))
  (is (false? (executable/compatible? 2 3)))
  ;; overlapping activities: greedy picks [1 3] [3 5] [5 7] = 3
  (is (= 3 (count (executable/select-activities [[1 3] [2 5] [3 5] [5 7] [4 7]])))))
