(ns rainbow.algorithms.proofs.particle-swarm-convex-trajectory-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.particle-swarm-convex-trajectory :as trajectory]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (trajectory/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest normalized-convex-swarm-trajectories-remain-in-the-invariant-interval
  (let [checked-environment @checked-environment
        definitions (trajectory/definition-ids checked-environment)
        theorems (trajectory/theorem-ids checked-environment)]
    (is (= #{'swarm/nnrat-convex-trajectory}
           (set (keys definitions))))
    (is (= #{'swarm/nnrat-convex-trajectory-zero
             'swarm/nnrat-convex-trajectory-successor
             'swarm/nnrat-convex-trajectory-lower-bound
             'swarm/nnrat-convex-trajectory-upper-bound
             'swarm/nnrat-convex-trajectory-in-interval}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
