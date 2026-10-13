(ns rainbow.math.finite.markov-reachability-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-reachability :as reachability]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (reachability/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-step-reachability-and-irreducibility-are-axiom-free
  (let [env @checked-environment
        definitions (reachability/definition-ids env)
        theorems (reachability/theorem-ids env)]
    (is (= #{'markov/nnrat-reachable
             'markov/nnrat-irreducible}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-reachable-reflexive
             'markov/nnrat-reachable-of-positive-entry
             'markov/nnrat-reachable-along-positive-trajectory
             'markov/nnrat-pointwise-positive-implies-irreducible}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
