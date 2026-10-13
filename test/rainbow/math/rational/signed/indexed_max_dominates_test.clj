(ns rainbow.math.rational.signed.indexed-max-dominates-test
  "Cold gate: indexed-max dominates every index below n (full argmax property), axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.indexed-max-dominates :as m]))
(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "checkpoint" {})))
           (m/extend-environment (:environment cp)))))
(deftest dominates-checked-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= #{'signed/indexed-max-from-dominates} (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d))))) (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
