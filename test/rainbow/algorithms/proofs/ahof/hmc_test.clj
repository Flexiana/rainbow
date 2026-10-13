(ns rainbow.algorithms.proofs.ahof.hmc-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.hmc :as hmc]
            [rainbow.algorithms.reference.hmc :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          hmc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hmc-drift-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hmc/definition-ids checked-environment)
        theorems (hmc/theorem-ids checked-environment)]
    (is (= #{'hmc/drift} (set (keys definitions))))
    (is (= #{'hmc/drift-unfold
             'hmc/drift-unit-2d-example
             'hmc/drift-unit-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hmc-leapfrog
  (is (= [3 2] (executable/drift [0 0] 1 [3 2])))
  ;; One leapfrog step for U(q) = (1/2)|q|^2 (grad = q) from q=[0], p=[2],
  ;; step 1: p-half = 2 - 1/2*0 = 2; q' = 0 + 1*2 = 2; p' = 2 - 1/2*2 = 1.
  (let [[q p] (executable/leapfrog [0] [2] (fn [q] q) 1)]
    (is (= [2] q))
    (is (= [1] p))))
