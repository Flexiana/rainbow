(ns rainbow.algorithms.proofs.ahof.failure-probability-monitor-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.failure-probability-monitor :as specialization]
            [rainbow.algorithms.proofs.failure-probability-monitor :as iteration]
            [rainbow.algorithms.reference.failure-probability-monitor :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          specialization/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest failure-monitor-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (iteration/definition-ids env) (iteration/theorem-ids env)
                   (specialization/definition-ids env)
                   (specialization/theorem-ids env))]
    (is (= #{'failmon/safe? 'failmon/alarm?
             'failmon/safe-unfold 'failmon/alarm-unfold
             'ahof-v64/threshold 'ahof-v64/low-is-safe 'ahof-v64/low-no-alarm
             'ahof-v64/high-is-unsafe 'ahof-v64/high-alarms
             'ahof-v64/failure-monitor}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-failure-monitor-matches-worked-instance
  ;; threshold 1/2
  (is (true? (executable/safe? 1/4 1/2)))
  (is (false? (executable/alarm? 1/4 1/2)))
  (is (false? (executable/safe? 3/4 1/2)))
  (is (true? (executable/alarm? 3/4 1/2))))
