(ns rainbow.algorithms.proofs.sarsa-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.sarsa :as ahof-d62]
            [rainbow.algorithms.proofs.sarsa :as iteration]
            [rainbow.algorithms.reference.sarsa :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d7-importance-sampling/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D7 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d62/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest sarsa-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'learning/signed-sarsa-update} (set (keys definitions))))
    (is (= #{'learning/signed-sarsa-update-unfold
             'learning/signed-sarsa-equals-q-update}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d62-sarsa-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d62/theorem-ids checked-environment)]
    (is (= #{'ahof-d62/updated-is-one-half
             'ahof-d62/coincides-with-q-update
             'ahof-d62/sarsa}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-sarsa-updates-on-policy
  ;; Rate 1/2, reward 1, discount 1, on-policy next 0, current 0: the TD error is
  ;; (1 + 1*0) - 0 = 1 and the update raises the value to 0 + (1/2)*1 = 1/2.
  (is (= 1 (executable/td-error 1 1 0 0)))
  (is (= 1/2 (executable/sarsa-update 1/2 1 1 0 0)))
  ;; A nonzero next value bootstraps a larger update.
  (is (= 1 (executable/sarsa-update 1/2 1 1 1 0))))
