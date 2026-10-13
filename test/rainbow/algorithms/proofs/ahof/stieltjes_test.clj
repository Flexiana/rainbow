(ns rainbow.algorithms.proofs.ahof.stieltjes-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.stieltjes :as stieltjes]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (stieltjes/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest stieltjes-three-term-recurrence-is-native-and-axiom-free
  (testing "the third deferred signed-cluster algorithm: the orthogonal-
            polynomial three-term recurrence (x-alpha)*p1 - beta*p2, one
            step proved by cross-product reflexivity"
    (let [env @checked-environment
          ids (merge (stieltjes/definition-ids env) (stieltjes/theorem-ids env))]
      (is (= #{'optimization/stieltjes-step
               'optimization/stieltjes-step-worked
               'optimization/stieltjes-step-preserves-zero}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
