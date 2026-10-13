(ns rainbow.algorithms.proofs.ahof.nnls-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.nnls :as nnls]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (nnls/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest nnls-projection-is-native-and-axiom-free
  (testing "the second deferred signed-cluster algorithm: nonnegative
            projection max(x,0), both branches proved -- positive passes
            through, negative projects to zero"
    (let [env @checked-environment
          ids (merge (nnls/definition-ids env) (nnls/theorem-ids env))]
      (is (= #{'optimization/nnls-project
               'optimization/nnls-project-positive-worked
               'optimization/nnls-project-negative-worked
               'optimization/nnls-project-nonnegative
               'optimization/nnls-project-fixes-nonnegative}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
