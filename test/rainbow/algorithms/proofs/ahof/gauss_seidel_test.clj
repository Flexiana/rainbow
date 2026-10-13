(ns rainbow.algorithms.proofs.ahof.gauss-seidel-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gauss-seidel :as gauss-seidel]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (gauss-seidel/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest gauss-seidel-coordinate-update-is-native-and-axiom-free
  (testing "the last deferred signed-cluster algorithm: the Gauss-Seidel
            coordinate update (b - offdiag) / diagonal, expressed with an
            nnrat reciprocal so no signed division is needed, worked step
            proved by cross-product reflexivity"
    (let [env @checked-environment
          ids (merge (gauss-seidel/definition-ids env)
                     (gauss-seidel/theorem-ids env))]
      (is (= #{'optimization/gauss-seidel-step
               'optimization/gauss-seidel-step-worked
               'optimization/gauss-seidel-step-exact}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
