(ns rainbow.algorithms.proofs.particle-swarm-best-iterate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.particle-swarm-best-iterate :as best-iterate]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (best-iterate/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-horizon-best-so-far-is-certified
  (let [checked-environment @checked-environment
        definitions (best-iterate/definition-ids checked-environment)
        theorems (best-iterate/theorem-ids checked-environment)]
    (is (= #{'swarm/nnrat-best-iterate}
           (set (keys definitions))))
    (is (= #{'swarm/nnrat-best-iterate-zero
             'swarm/nnrat-best-iterate-successor
             'swarm/nnrat-best-iterate-successor-is-previous-or-proposal
             'swarm/nnrat-best-iterate-successor-bounds-previous
             'swarm/nnrat-best-iterate-successor-bounds-proposal
             'swarm/nnrat-best-iterate-bounds-initial}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
