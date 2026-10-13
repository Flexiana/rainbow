(ns rainbow.algorithms.proofs.ahof.baseline-subtraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.baseline-subtraction :as baseline]
            [rainbow.algorithms.reference.baseline-subtraction :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          baseline/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest baseline-subtraction-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (baseline/definition-ids checked-environment)
        theorems (baseline/theorem-ids checked-environment)]
    (is (= #{'baseline/contribution} (set (keys definitions))))
    (is (= #{'baseline/contribution-unfold
             'baseline/contribution-example
             'baseline/zero-advantage-cancels}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-baseline-subtraction-reduces-variance
  (is (= 12 (executable/contribution 3 4)))
  (is (= 0 (executable/contribution 0 9)))
  ;; With baseline 5, trajectory returns (6,4,5) and scores (2,1,9): advantages
  ;; (1,-1,0), contributions (2,-1,0), mean 1/3.
  (is (= 1/3 (executable/baselined-gradient 5 [[6 2] [4 1] [5 9]]))))
