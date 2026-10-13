(ns rainbow.algorithms.proofs.ahof.gradient-boosting-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gradient-boosting :as gb]
            [rainbow.algorithms.reference.gradient-boosting :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gb/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gradient-boosting-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gb/definition-ids checked-environment)
        theorems (gb/theorem-ids checked-environment)]
    (is (= #{'gradient-boosting/update} (set (keys definitions))))
    (is (= #{'gradient-boosting/boost-step-example
             'gradient-boosting/zero-rate-unchanged}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gradient-boosting
  (is (= 5/2 (executable/boost-update 2 1/2 1)))
  (is (= 3 (executable/boost-update 3 0 9)))
  ;; from 0, rate 1/2, weak predictions [2 2 2]: 0 + 1/2*2 *3 = 3
  (is (= 3 (executable/boost 0 1/2 [2 2 2]))))
