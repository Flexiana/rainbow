(ns rainbow.algorithms.proofs.ahof.lqr-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.lqr :as lqr]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lqr/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest lqr-linear-feedback-is-native-and-axiom-free
  (testing "the signed-cluster deferred algorithm now buildable: LQR
            u = -Kx as a composition of signed scale and negate, worked
            instance proved by cross-product reflexivity"
    (let [env @checked-environment
          ids (merge (lqr/definition-ids env) (lqr/theorem-ids env))]
      (is (= #{'control/lqr-action 'control/lqr-action-worked
               'control/lqr-action-sign-reversing}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
