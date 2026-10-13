(ns rainbow.algorithms.proofs.ahof.accuracy-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.accuracy :as acc]
            [rainbow.algorithms.reference.accuracy :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          acc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest accuracy-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (acc/definition-ids checked-environment)
        theorems (acc/theorem-ids checked-environment)]
    (is (= #{'accuracy/accuracy} (set (keys definitions))))
    (is (= #{'accuracy/accuracy-example 'accuracy/perfect-classifier-accuracy-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-accuracy
  (is (= 3/4 (executable/accuracy 3 4)))
  (is (= 1 (executable/accuracy 5 5)))
  ;; 3 of 4 predictions correct
  (is (= 3/4 (executable/score [1 0 1 1] [1 0 0 1]))))
