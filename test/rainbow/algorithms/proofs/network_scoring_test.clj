(ns rainbow.algorithms.proofs.network-scoring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.network-scoring :as ahof-d14]
            [rainbow.algorithms.proofs.network-scoring :as iteration]
            [rainbow.algorithms.reference.network-scoring :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/v26-monte-carlo/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "V26 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d14/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest network-scoring-is-native-axiom-free-and-decomposable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'scoring/nnrat-total-score} (set (keys definitions))))
    (is (= #{'scoring/score-empty 'scoring/score-cons}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d14-score-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d14/theorem-ids checked-environment)]
    (is (= #{'ahof-d14/score-is-one 'ahof-d14/network-scoring}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-network-score-is-additive-and-exact
  (let [local (fn [n] (case n 0 1/2 1 1/4 2 1/4))]
    (is (= 1 (executable/total-score local [0 1 2])))
    ;; Additive decomposition: adding node 0 adds exactly its local score.
    (is (= (executable/total-score local [0 1 2])
           (+ (executable/add-node-delta local 0)
              (executable/total-score local [1 2]))))))
