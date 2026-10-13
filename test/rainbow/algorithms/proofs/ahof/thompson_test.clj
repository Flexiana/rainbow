(ns rainbow.algorithms.proofs.ahof.thompson-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.thompson :as thompson]
            [rainbow.algorithms.reference.thompson :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          thompson/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest thompson-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (thompson/definition-ids checked-environment)
        theorems (thompson/theorem-ids checked-environment)]
    (is (= #{'thompson/select} (set (keys definitions))))
    (is (= #{'thompson/selects-largest-sample
             'thompson/selected-dominates-arm-zero
             'thompson/selected-dominates-arm-two}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-thompson-selects
  (is (= 1 (executable/thompson-select [5 8 4])))
  (is (= 2 (executable/thompson-select [1 3 9])))
  ;; identity sampler over posterior "means"
  (is (= 0 (executable/select-from-posteriors [7 2 5] identity))))
