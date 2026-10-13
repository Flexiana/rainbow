(ns rainbow.algorithms.proofs.ahof.qmdp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.qmdp :as qmdp]
            [rainbow.algorithms.reference.qmdp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          qmdp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest qmdp-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (qmdp/definition-ids checked-environment)
        theorems (qmdp/theorem-ids checked-environment)]
    (is (= #{'qmdp/value} (set (keys definitions))))
    (is (= #{'qmdp/value-example 'qmdp/certain-belief} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-qmdp-value
  (is (= 2 (executable/qmdp-value 1/2 1 1/2 3)))
  (is (= 5 (executable/qmdp-value 1 5 0 9)))
  (is (= 2 (executable/qmdp-action-value [1/2 1/2] [1 3]))))
