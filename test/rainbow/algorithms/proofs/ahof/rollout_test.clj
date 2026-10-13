(ns rainbow.algorithms.proofs.ahof.rollout-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.rollout :as rollout]
            [rainbow.algorithms.reference.rollout :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rollout/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rollout-return-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rollout/definition-ids checked-environment)
        theorems (rollout/theorem-ids checked-environment)]
    (is (= #{'rollout/trajectory-return} (set (keys definitions))))
    (is (= #{'rollout/trajectory-return-unfold
             'rollout/trajectory-return-example
             'rollout/return-dominates-step}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-rollout-estimates-value
  (is (= 7 (executable/trajectory-return 3 4)))
  ;; Discounted return of [4 4 4] at gamma 1/2: 4 + 2 + 1 = 7.
  (is (= 7 (executable/simulate-return [4 4 4] 1/2)))
  ;; Mean over three identical rollouts is the single return.
  (is (= 7 (executable/estimate-value (fn [] [4 4 4]) 1/2 3))))
