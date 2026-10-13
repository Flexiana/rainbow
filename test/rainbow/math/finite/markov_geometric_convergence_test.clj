(ns rainbow.math.finite.markov-geometric-convergence-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-geometric-convergence :as convergence]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (convergence/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest geometric-convergence-combines-both-bricks-at-the-stationary-target
  (testing "brick 3: iterates of any equal-mass start converge to the
            stationary distribution inside an explicit rho^n envelope --
            brick 1 fixes the target under iteration, brick 2 supplies the
            decay, one replayed environment carries the whole chain"
    (let [env @checked-environment
          ids (merge (convergence/definition-ids env)
                     (convergence/theorem-ids env))]
      (is (= #{'markov/nnrat-kernel-iterate-geometric-convergence-to-stationary}
             (set (keys ids))))
      (doseq [dependency '[markov/nnrat-kernel-iterate-total-variation-decay
                           markov/nnrat-stationary-iterate-fixed
                           markov/nnrat-dobrushin-contraction
                           nnrat/power]]
        (is (some? (environment/resolve-id env dependency)) (str dependency)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
