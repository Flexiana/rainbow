(ns rainbow.algorithms.proofs.ahof.reachability-eda-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.reachability-eda :as re]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (re/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest reachability-eda-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (re/definition-ids env) (re/theorem-ids env))]
    (is (= #{'boolean/or 'reach/backward-reachable 'reach/conservative-upper
             'opt/asa-accept 'eda/grammar-update 'eda/pipe-update
             'boolean/or-true-left 'reach/backward-reach-from-successor
             'reach/conservative-upper-example 'opt/asa-accept-not-worse
             'eda/grammar-update-within-max 'eda/pipe-update-within-max}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
