(ns rainbow.algorithms.proofs.ahof.trpo-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.trpo :as trpo]
            [rainbow.algorithms.reference.trpo :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          trpo/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest trpo-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (trpo/definition-ids checked-environment)
        theorems (trpo/theorem-ids checked-environment)]
    (is (= #{'trpo/within-trust-region?} (set (keys definitions))))
    (is (= #{'trpo/update-admissible 'trpo/admitted-stays-in-region
             'trpo/oversized-update-rejected}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-trpo-admits-within-region
  (is (true? (executable/within-trust-region? 1/10 1/4)))
  (is (false? (executable/within-trust-region? 1/2 1/4)))
  ;; backtracking: full step KL scales with fraction^2 here; delta 1/4
  (is (= 1/2 (executable/admit-step #(* % %) 1/4 [1 1/2 1/4]))))
