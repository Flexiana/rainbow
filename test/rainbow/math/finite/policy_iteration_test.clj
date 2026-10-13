(ns rainbow.math.finite.policy-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.policy-iteration :as ahof-d21]
            [rainbow.math.finite.policy-iteration :as iteration]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d20-policy-evaluation/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D20 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d21/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-policy-improvement-is-native-axiom-free-and-transferable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'policy/nnrat-improve 'policy/nnrat-iteration-step}
           (set (keys definitions))))
    (is (= #{'nnrat/equivalent-to-at-most
             'nnrat/at-most-respects-equivalence
             'policy/nnrat-improve-is-admissible
             'policy/nnrat-improve-dominates
             'policy/nnrat-iteration-step-unfold
             'policy/nnrat-improvement-model-transfer
             'policy/nnrat-improvement-state-transfer}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest ahof-d21-composes-evaluation-and-improvement
  (let [checked-environment @checked-environment
        theorems (ahof-d21/theorem-ids checked-environment)]
    (is (= #{'ahof-d21/current-policy-admissible
             'ahof-d21/evaluation-phase
             'ahof-d21/improvement-phase
             'ahof-d21/policy-iteration-step}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
