(ns rainbow.algorithms.proofs.ahof.kalman-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kalman :as kalman]
            [rainbow.algorithms.reference.kalman :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kalman/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kalman-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kalman/definition-ids checked-environment)
        theorems (kalman/theorem-ids checked-environment)]
    (is (= #{'kalman/gain 'kalman/posterior} (set (keys definitions))))
    (is (= #{'kalman/balanced-gain 'kalman/balanced-posterior
             'kalman/confident-measurement-gain}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kalman-update
  (is (= 1/2 (executable/kalman-gain 1 1)))
  (is (= 1/2 (executable/kalman-posterior 1 1)))
  (is (= 3/4 (executable/kalman-gain 3 1)))
  ;; measurement z=2 from prior x=0, P=R=1: 0 + 1/2*(2-0) = 1
  (is (= 1 (executable/update-mean 0 1 2 1))))
