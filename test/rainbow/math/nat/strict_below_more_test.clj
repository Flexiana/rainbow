(ns rainbow.math.nat.strict-below-more-test
  "Cold gate: add-successor-right, strict-below-self, strict-below-weaken. Axiom-free."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.strict-below-more :as m]))
(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "checkpoint" {})))
           (m/extend-environment (:environment cp)))))
(deftest nat-helpers-checked-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= #{'nat/add-successor-right 'nat/strict-below-self 'nat/strict-below-weaken} (set (keys ids))))
    (doseq [[nm id] ids]
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d))))) (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))
