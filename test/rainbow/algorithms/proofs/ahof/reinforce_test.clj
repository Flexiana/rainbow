(ns rainbow.algorithms.proofs.ahof.reinforce-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.reinforce :as reinforce]
            [rainbow.algorithms.reference.reinforce :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          reinforce/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest reinforce-estimate-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (reinforce/definition-ids checked-environment)
        theorems (reinforce/theorem-ids checked-environment)]
    (is (= #{'reinforce/estimate} (set (keys definitions))))
    (is (= #{'reinforce/estimate-unfold
             'reinforce/estimate-example
             'reinforce/zero-return-ignored}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reinforce-estimates-gradient
  (is (= 10 (executable/estimate-two 2 3 1 4)))
  (is (= 4 (executable/estimate-two 0 9 1 4)))
  ;; Batch mean of return*score over three trajectories: (6 + 4 + 2)/3 = 4.
  (is (= 4 (executable/gradient [[2 3] [1 4] [1 2]]))))
