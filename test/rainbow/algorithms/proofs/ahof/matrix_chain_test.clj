(ns rainbow.algorithms.proofs.ahof.matrix-chain-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.matrix-chain :as mcm]
            [rainbow.algorithms.reference.matrix-chain :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mcm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest matrix-chain-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mcm/definition-ids checked-environment)
        theorems (mcm/theorem-ids checked-environment)]
    (is (= #{'matrix-chain/split-cost 'matrix-chain/better-split}
           (set (keys definitions))))
    (is (= #{'matrix-chain/split-cost-example 'matrix-chain/takes-cheaper-split
             'matrix-chain/chosen-split-is-minimal}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-matrix-chain
  (is (= 9 (executable/split-cost 2 3 4)))
  (is (= 6 (executable/better-split 9 6)))
  ;; classic example dims [10 30 5 60]: optimal 4500
  (is (= 4500 (executable/min-mults [10 30 5 60]))))
