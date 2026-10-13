(ns rainbow.algorithms.proofs.ahof.policy-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.policy-gradient :as policy-gradient]
            [rainbow.algorithms.reference.policy-gradient :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          policy-gradient/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest policy-gradient-update-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (policy-gradient/definition-ids checked-environment)
        theorems (policy-gradient/theorem-ids checked-environment)]
    (is (= #{'policy-gradient/update} (set (keys definitions))))
    (is (= #{'policy-gradient/update-unfold
             'policy-gradient/update-unit-2d-example
             'policy-gradient/update-unit-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-policy-gradient-ascends
  (is (= [3 2] (executable/update-step [0 0] 1 [3 2])))
  ;; A constant gradient accumulates linearly over the ascent.
  (is (= [6 4] (executable/ascend (constantly [3 2]) [0 0] 1 2)))
  (is (= [0 0] (executable/ascend (constantly [3 2]) [0 0] 1 0))))
