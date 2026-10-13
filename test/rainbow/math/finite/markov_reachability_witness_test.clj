(ns rainbow.math.finite.markov-reachability-witness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-reachability-witness
             :as reachability-witness]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (reachability-witness/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest canonical-zero-and-one-step-support-witnesses-are-axiom-free
  (let [env @checked-environment
        definitions (reachability-witness/definition-ids env)
        theorems (reachability-witness/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'markov/nnrat-positive-entry-iterate-witness
             'markov/nnrat-point-mass-reflexive-iterate-witness}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
