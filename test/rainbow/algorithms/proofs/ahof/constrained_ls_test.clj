(ns rainbow.algorithms.proofs.ahof.constrained-ls-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.constrained-ls :as cl]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (cl/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest constrained-ls-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (cl/definition-ids env) (cl/theorem-ids env))]
    (is (= #{'opt/lsi-feasible 'opt/ldp-min-norm 'opt/admm-consensus
             'opt/lsi-feasible-sound 'opt/ldp-below-left 'opt/ldp-below-right
             'opt/admm-consensus-within-max}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
