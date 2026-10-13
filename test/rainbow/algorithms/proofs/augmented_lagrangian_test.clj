(ns rainbow.algorithms.proofs.augmented-lagrangian-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.augmented-lagrangian :as lagrangian]
            [rainbow.algorithms.reference.augmented-lagrangian :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (lagrangian/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest lagrangian-multiplier-update-is-native-axiom-free
  (let [env @checked-environment
        definitions (lagrangian/definition-ids env)
        theorems (lagrangian/theorem-ids env)]
    (is (= #{'lagrangian/update-multiplier} (set (keys definitions))))
    (is (= #{'lagrangian/update-multiplier-unfold
             'lagrangian/violation-raises-example
             'lagrangian/over-satisfied-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-augmented-lagrangian-updates-multiplier-exactly
  ;; Positive violation raises the multiplier: 1 + 2*1 = 3.
  (is (= 3 (executable/update-multiplier 1 2 1)))
  ;; Over-satisfied (negative violation) lowers it: 3 + 1*(-1) = 2.
  (is (= 2 (executable/update-multiplier 3 1 -1)))
  ;; A feasible constraint leaves the multiplier unchanged.
  (is (= 5 (executable/update-multiplier 5 2 0)))
  ;; The augmented value: f=1, lambda=2, rho=2, c=1: 1 + 2*1 + 1*1 = 4.
  (is (= 4 (executable/augmented-value 1 2 2 1))))
