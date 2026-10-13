(ns rainbow.algorithms.proofs.ahof.reliability-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.reliability :as reliability]
            [rainbow.algorithms.reference.reliability :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          reliability/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest reliability-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (reliability/definition-ids checked-environment)
        theorems (reliability/theorem-ids checked-environment)]
    (is (= #{'reliability/series 'reliability/meets-requirement?}
           (set (keys definitions))))
    (is (= #{'reliability/series-example 'reliability/perfect-series
             'reliability/meets-target 'reliability/passing-meets-threshold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reliability
  (is (= 1/4 (executable/series-reliability [1/2 1/2])))
  (is (= 1 (executable/series-reliability [1 1 1])))
  (is (true? (executable/meets-requirement? 3/4 1/2)))
  ;; parallel of two 1/2-reliable components: 1 - (1/2)(1/2) = 3/4
  (is (= 3/4 (executable/parallel-reliability [1/2 1/2]))))
