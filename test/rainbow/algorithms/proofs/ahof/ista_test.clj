(ns rainbow.algorithms.proofs.ahof.ista-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.ista :as ista]
            [rainbow.algorithms.reference.ista :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ista/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest ista-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ista/definition-ids checked-environment)
        theorems (ista/theorem-ids checked-environment)]
    (is (= #{'ista/shrinks-to-zero?} (set (keys definitions))))
    (is (= #{'ista/small-coefficient-zeroed 'ista/zeroed-within-threshold
             'ista/large-coefficient-survives}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-ista-soft-threshold
  (is (true? (executable/shrinks-to-zero? 1/4 1/2)))
  (is (false? (executable/shrinks-to-zero? 3/4 1/2)))
  (is (= 0 (executable/soft-threshold 1/4 1/2)))
  (is (= 1/4 (executable/soft-threshold 3/4 1/2)))
  (is (= -1/4 (executable/soft-threshold -3/4 1/2))))
