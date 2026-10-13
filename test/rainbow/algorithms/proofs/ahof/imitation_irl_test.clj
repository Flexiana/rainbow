(ns rainbow.algorithms.proofs.ahof.imitation-irl-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.imitation-irl :as ii]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (ii/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest imitation-irl-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (ii/definition-ids env) (ii/theorem-ids env))]
    (is (= #{'irl/smile-mixture 'irl/margin-satisfied 'irl/maxent-probability 'learn/structure-accept
             'irl/smile-within-max 'irl/margin-sound 'irl/maxent-probability-example
             'learn/structure-improves}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
