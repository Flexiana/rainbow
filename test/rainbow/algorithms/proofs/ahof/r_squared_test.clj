(ns rainbow.algorithms.proofs.ahof.r-squared-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.r-squared :as r2]
            [rainbow.algorithms.reference.r-squared :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          r2/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest r-squared-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (r2/definition-ids checked-environment)
        theorems (r2/theorem-ids checked-environment)]
    (is (= #{'r-squared/r-squared} (set (keys definitions))))
    (is (= #{'r-squared/r-squared-example 'r-squared/perfect-fit-r-squared-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-r-squared
  (is (= 3/4 (executable/r-squared 3 4)))
  (is (= 1 (executable/r-squared 5 5)))
  ;; perfect predictions -> R^2 = 1
  (is (= 1 (executable/score [1 2 3 4] [1 2 3 4])))
  ;; predicting the mean -> R^2 = 0
  (is (= 0 (executable/score [1 2 3 4] [5/2 5/2 5/2 5/2]))))
