(ns rainbow.algorithms.proofs.particle-swarm-projected-trajectory-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.particle-swarm-projected-trajectory :as projected]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (projected/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest projected-particle-trajectories-are-box-bounded
  (let [checked-environment @checked-environment
        definitions (projected/definition-ids checked-environment)
        theorems (projected/theorem-ids checked-environment)]
    (is (= #{'swarm/projected-step
             'swarm/projected-trajectory}
           (set (keys definitions))))
    (is (= #{'swarm/projected-step-unfold
             'swarm/projected-step-in-band
             'swarm/projected-trajectory-zero
             'swarm/projected-trajectory-successor
             'swarm/projected-trajectory-successor-in-band
             'swarm/projected-trajectory-in-band}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
