(ns rainbow.math.finite.markov-ergodic-uniqueness-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-ergodic-uniqueness :as uniqueness]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (uniqueness/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest ergodic-uniqueness-is-unconditional-and-axiom-free
  (testing "the capstone with no open inequality beneath it: a certified
            Dobrushin bound below one forces any two equal-mass stationary
            distributions to agree pointwise -- one environment carrying the
            contraction inhabitant, the conditional theorem, and their whole
            combined chain, replayed from D63"
    (let [env @checked-environment
          ids (merge (uniqueness/definition-ids env)
                     (uniqueness/theorem-ids env))]
      (is (= #{'markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound}
             (set (keys ids))))
      ;; The two halves this composes must be present in the same world.
      (doseq [dependency '[markov/nnrat-dobrushin-contraction
                           markov/nnrat-dobrushin-contraction-estimate
                           markov/nnrat-stationary-pointwise-unique-of-proper-contraction
                           nnrat/zero-of-proper-contraction]]
        (is (some? (environment/resolve-id env dependency)) (str dependency)))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
