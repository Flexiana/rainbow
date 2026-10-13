(ns rainbow.math.rational.signed.reciprocal-absolute-bound-test
  "Cold gate for the orphaned work-in-progress brick (Layer A of the limit-reciprocal assembly), axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.reciprocal-absolute-bound :as m]))
(def checked-environment
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp)) (throw (ex-info "checkpoint" {})))
      (m/extend-environment (:environment cp)))))
(deftest reciprocal-absolute-bound-checked-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= #{'signed/absolute-reciprocal-at-most-of-lower-bound} (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d))))) (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
