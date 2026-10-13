(ns rainbow.math.finite.markov-geometric-decay-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-geometric-decay :as decay]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (decay/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest geometric-decay-composes-the-inhabitant-with-the-iterate-laws
  (testing "brick 2 of the convergence half: total variation between n-th
            iterates decays as rho^n, built directly on the landed
            contraction inhabitant, the iterate laws, and the exact power --
            one environment, replayed from D63"
    (let [env @checked-environment
          ids (merge (decay/definition-ids env) (decay/theorem-ids env))]
      (is (= #{'markov/nnrat-kernel-iterate-total-variation-decay}
             (set (keys ids))))
      (doseq [dependency '[markov/nnrat-dobrushin-contraction
                           markov/nnrat-kernel-iterate-successor
                           markov/nnrat-kernel-iterate-preserves-total-mass-equivalence
                           nnrat/power]]
        (is (some? (environment/resolve-id env dependency)) (str dependency)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
