(ns rainbow.algorithms.proofs.reward-to-go-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.reward-to-go :as reward-to-go]
            [rainbow.algorithms.reference.reward-to-go :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          reward-to-go/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest reward-to-go-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (reward-to-go/definition-ids checked-environment)
        theorems (reward-to-go/theorem-ids checked-environment)]
    (is (= #{'reward-to-go/reward-to-go} (set (keys definitions))))
    (is (= #{'reward-to-go/suffix-recurrence
             'reward-to-go/full-return-example
             'reward-to-go/suffix-return-example
             'reward-to-go/empty-return-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reward-to-go-matches-the-suffix-sum
  (is (= 6 (executable/reward-to-go [3 2 1])))
  (is (= 3 (executable/reward-to-go [2 1])))
  (is (= 0 (executable/reward-to-go [])))
  ;; One backward pass yields the reward-to-go at every step.
  (is (= [6 3 1] (executable/to-go-sequence [3 2 1])))
  (is (= [3 1] (executable/to-go-sequence [2 1]))))
