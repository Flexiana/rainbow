(ns rainbow.algorithms.proofs.ahof.projection-methods-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.projection-methods :as pm]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (pm/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest projection-methods-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (pm/definition-ids env) (pm/theorem-ids env))]
    (is (= #{'opt/projected-gradient-step 'policy/restricted-gradient-step 'opt/lp-round
             'opt/projected-below-hi 'opt/projected-above-lo
             'policy/restricted-within-trust-hi 'policy/restricted-within-trust-lo
             'opt/lp-round-up-example 'opt/lp-round-down-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
