(ns rainbow.algorithms.proofs.ahof.rbf-surrogate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.rbf-surrogate :as rbf]
            [rainbow.algorithms.reference.rbf-surrogate :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rbf/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rbf-prediction-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rbf/definition-ids checked-environment)
        theorems (rbf/theorem-ids checked-environment)]
    (is (= #{'rbf/predict} (set (keys definitions))))
    (is (= #{'rbf/predict-unfold 'rbf/predict-example 'rbf/predict-single-basis}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-rbf-predicts-by-weighted-sum
  (is (= 10 (executable/predict-two 2 3 1 4)))
  (is (= 6 (executable/predict-two 2 3 0 4)))
  (is (= 10 (executable/predict [2 1] [3 4])))
  (is (= 20 (executable/predict [2 1 3] [3 4 10/3]))))
