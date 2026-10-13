(ns rainbow.math.finite.bellman-value-optimality-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-value-optimality :as optimality]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (optimality/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest normalized-expectation-and-bellman-contraction-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (optimality/definition-ids env)
                   (optimality/theorem-ids env))]
    (is (= #{'probability/nnrat-total-mass
             'markov/nnrat-rows-normalized
             'value/nnrat-contraction-radius
             'nnrat/multiply-distributes-add-left
             'probability/nnrat-expectation-add-constant
             'probability/nnrat-expectation-additive-upper-bound-normalized
             'bellman/nnrat-action-backup-additive-upper-bound
             'bellman/nnrat-action-backup-additively-contractive
             'value/nnrat-optimality-step-additively-contractive
             'analysis/nnrat-contraction-radius-converges}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
