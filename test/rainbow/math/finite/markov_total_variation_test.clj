(ns rainbow.math.finite.markov-total-variation-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-total-variation :as total-variation]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (total-variation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest the-total-variation-bridgehead-is-native-and-axiom-free
  (testing "the L1 distance, the zero-sum-zero-terms lemma, the pointwise
            congruence, symmetry, both zero directions, and the stationary
            separation capstone -- with the Dobrushin contraction deliberately
            absent and named as the single remaining inequality"
    (let [env @checked-environment
          ids (merge (total-variation/definition-ids env)
                     (total-variation/theorem-ids env))]
      (is (= 7 (count ids)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
