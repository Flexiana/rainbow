(ns rainbow.algorithms.proofs.decision-network-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.decision-network :as ahof-d18]
            [rainbow.algorithms.proofs.decision-network :as iteration]
            [rainbow.algorithms.reference.decision-network :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d25-nearest-neighbor/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D25 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d18/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest decision-network-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'decision/network-value} (set (keys definitions))))
    (is (= #{'decision/network-value-unfold} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d18-decision-network-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d18/theorem-ids checked-environment)]
    (is (= #{'ahof-d18/network-eu-is-three-quarters
             'ahof-d18/utility-at-zero-is-one
             'ahof-d18/utility-at-one-is-zero
             'ahof-d18/decision-network}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-decision-network-is-expected-utility
  ;; Two outcomes with probabilities 3/4 and 1/4, utilities 1 and 0: the expected
  ;; utility is 3/4 * 1 + 1/4 * 0 = 3/4.
  (let [probability (fn [o] (case o 0 3/4 1 1/4 0))
        utility (fn [o] (case o 0 1 1 0 0))]
    (is (= 3/4 (executable/network-value [0 1] probability utility)))
    ;; A different utility node changes the evaluation.
    (is (= 1/4 (executable/network-value [0 1] probability
                                         (fn [o] (case o 0 0 1 1 0)))))))
