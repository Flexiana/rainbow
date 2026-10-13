(ns rainbow.algorithms.proofs.exact-inference-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.exact-inference :as ahof-d2]
            [rainbow.algorithms.proofs.exact-inference :as iteration]
            [rainbow.algorithms.reference.exact-inference :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d49-gradient-ascent/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D49 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d2/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest exact-inference-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'inference/nnrat-joint 'inference/nnrat-marginal}
           (set (keys definitions))))
    (is (= #{'inference/nnrat-joint-unfold
             'inference/nnrat-marginal-unfold
             'inference/nnrat-marginal-is-enumerated-joint
             'inference/nnrat-marginal-transfer}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d2-network-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d2/theorem-ids checked-environment)]
    (is (= #{'ahof-d2/marginal-values
             'ahof-d2/normalization
             'ahof-d2/exact-inference}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reference-marginalizes-exactly
  (let [prior (constantly 1/2)
        likelihood-true (fn [a] (if (= a 0) 1/2 1))
        likelihood-false (fn [a] (if (= a 0) 1/2 0))]
    (is (= 3/4 (executable/marginal [0 1] prior likelihood-true)))
    (is (= 1/4 (executable/marginal [0 1] prior likelihood-false)))
    (is (= 1 (+ (executable/marginal [0 1] prior likelihood-true)
                (executable/marginal [0 1] prior likelihood-false))))))
