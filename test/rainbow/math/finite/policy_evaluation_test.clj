(ns rainbow.math.finite.policy-evaluation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.policy-evaluation :as ahof-d20]
            [rainbow.math.finite.policy-evaluation :as evaluation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d17-maximum-expected-utility/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D17 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          evaluation/extend-environment
          ahof-d20/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-policy-evaluation-lifts-congruence-across-all-finite-steps
  (let [checked-environment @checked-environment
        theorems (evaluation/theorem-ids checked-environment)]
    (is (= #{'nat/recursor-successor-constant
             'nat/iterate-related
             'bellman/nnrat-value-iterate-successor
             'bellman/nnrat-value-iterate-congruent
             'bellman/nnrat-value-iterate-model-transfer
             'bellman/nnrat-value-iterate-initial-transfer}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest ahof-d20-specialization-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d20/theorem-ids checked-environment)]
    (is (= #{'ahof-d20/finite-horizon-recurrence
             'ahof-d20/normalized-transition-rows
             'ahof-d20/one-step-value
             'ahof-d20/two-step-value
             'ahof-d20/policy-evaluation}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
