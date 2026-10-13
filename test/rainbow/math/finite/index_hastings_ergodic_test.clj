(ns rainbow.math.finite.index-hastings-ergodic-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.index-hastings-ergodic :as ergodic]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (ergodic/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest the-finite-ergodic-theorem-instantiates-for-hastings-kernels
  (testing "both halves of the theorem pair, specialized to the canonical
            Hastings kernel on Index(n+1): the executable full-support
            verdict certifies the proper factor, uniqueness and the
            geometric envelope follow -- the two worlds composed in one
            replayed environment"
    (let [env @checked-environment
          ids (merge (ergodic/definition-ids env) (ergodic/theorem-ids env))]
      (is (= #{'mcmc/nnrat-hastings-index-stationary-unique-of-full-support
               'mcmc/nnrat-hastings-index-geometric-convergence-of-full-support}
             (set (keys ids))))
      (doseq [dependency '[mcmc/nnrat-hastings-index-dobrushin-bound-of-full-support
                           markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound
                           markov/nnrat-kernel-iterate-geometric-convergence-to-stationary
                           markov/nnrat-dobrushin-contraction]]
        (is (some? (environment/resolve-id env dependency)) (str dependency)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
