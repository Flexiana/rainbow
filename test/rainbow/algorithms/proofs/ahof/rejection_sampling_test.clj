(ns rainbow.algorithms.proofs.ahof.rejection-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.rejection-sampling :as rejection]
            [rainbow.algorithms.reference.rejection-sampling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rejection/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest rejection-sampling-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rejection/definition-ids checked-environment)
        theorems (rejection/theorem-ids checked-environment)]
    (is (= #{'rejection/accepts?} (set (keys definitions))))
    (is (= #{'rejection/accepts-consistent
             'rejection/accepted-is-valid
             'rejection/rejects-inconsistent}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-rejection-sampling-retains-consistent-draws
  (is (true? (executable/accepts? 2 5)))
  (is (false? (executable/accepts? 8 5)))
  (is (= [2 4 1] (executable/sample identity 5 [2 8 4 6 1])))
  (is (= 3/5 (executable/acceptance-ratio identity 5 [2 8 4 6 1]))))
