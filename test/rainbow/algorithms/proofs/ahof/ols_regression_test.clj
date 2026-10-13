(ns rainbow.algorithms.proofs.ahof.ols-regression-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.ols-regression :as ols]
            [rainbow.algorithms.reference.ols-regression :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ols/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest ols-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ols/definition-ids checked-environment)
        theorems (ols/theorem-ids checked-environment)]
    (is (= #{'ols/slope} (set (keys definitions))))
    (is (= #{'ols/slope-example 'ols/unit-covariance-slope-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-ols
  (is (= 3/2 (executable/slope 3 2)))
  (is (= 1 (executable/slope 2 2)))
  ;; points on y = 2x + 1 exactly -> slope 2, intercept 1
  (is (= [2 1] (executable/fit [[0 1] [1 3] [2 5] [3 7]]))))
