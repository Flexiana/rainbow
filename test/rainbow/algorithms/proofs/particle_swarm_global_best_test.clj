(ns rainbow.algorithms.proofs.particle-swarm-global-best-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.particle-swarm-global-best :as global-best]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (global-best/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-particle-swarm-global-best-is-certified
  (let [checked-environment @checked-environment
        definitions (global-best/definition-ids checked-environment)
        theorems (global-best/theorem-ids checked-environment)]
    (is (= #{'swarm/nnrat-global-best
             'swarm/nnrat-best-so-far}
           (set (keys definitions))))
    (is (= #{'swarm/nnrat-global-best-unfold
             'swarm/nnrat-global-best-is-member
             'swarm/nnrat-global-best-dominates
             'swarm/nnrat-best-so-far-unfold
             'swarm/nnrat-best-so-far-is-previous-or-candidate
             'swarm/nnrat-best-so-far-bounds-previous
             'swarm/nnrat-best-so-far-bounds-candidate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
