(ns rainbow.algorithms.proofs.particle-swarm-convex-move-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.particle-swarm-convex-move :as move]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (move/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest convex-movement-toward-swarm-best-stays-between-endpoints
  (let [checked-environment @checked-environment
        definitions (move/definition-ids checked-environment)
        theorems (move/theorem-ids checked-environment)]
    (is (= #{'swarm/nnrat-convex-move}
           (set (keys definitions))))
    (is (= #{'swarm/nnrat-convex-move-unfold
             'swarm/nnrat-convex-move-lower-bound
             'swarm/nnrat-convex-move-upper-bound
             'swarm/nnrat-convex-move-between-position-and-best
             'swarm/nnrat-convex-move-between-best-and-position}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
