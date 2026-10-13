(ns rainbow.algorithms.reference.monte-carlo-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.monte-carlo :as ahof-v26]
            [rainbow.math.monte-carlo-estimation :as iteration]
            [rainbow.algorithms.reference.monte-carlo :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d61-q-learning/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D61 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-v26/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest monte-carlo-estimator-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'estimation/nnrat-indicator
             'estimation/failure-count
             'estimation/monte-carlo-frequency}
           (set (keys definitions))))
    (is (= #{'estimation/indicator-failure
             'estimation/indicator-success
             'estimation/count-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-v26-estimate-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-v26/theorem-ids checked-environment)]
    (is (= #{'ahof-v26/count-is-one
             'ahof-v26/estimate-is-quarter
             'ahof-v26/monte-carlo}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-monte-carlo-estimates-exactly
  ;; One failure in four samples is an exact 1/4 failure frequency.
  (is (= 1 (executable/failure-count [true false false false])))
  (is (= 1/4 (executable/failure-frequency [true false false false])))
  (is (= 1/2 (executable/failure-frequency [true false true false])))
  (is (= 0 (executable/failure-frequency [false false false]))))
