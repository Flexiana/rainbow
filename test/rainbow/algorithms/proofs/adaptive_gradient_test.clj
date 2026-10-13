(ns rainbow.algorithms.proofs.adaptive-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.adaptive-gradient :as adagrad]
            [rainbow.algorithms.reference.adaptive-gradient :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (adagrad/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest adagrad-square-root-and-rate-are-native-axiom-free
  (let [env @checked-environment
        definitions (adagrad/definition-ids env)
        theorems (adagrad/theorem-ids env)]
    (is (= #{'adagrad/square-root? 'adagrad/rate} (set (keys definitions))))
    (is (= #{'adagrad/two-is-root-of-four 'adagrad/three-is-root-of-nine
             'adagrad/rate-unfold 'adagrad/adaptive-rate-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-adagrad-adapts-rate-exactly
  ;; Perfect-square roots.
  (is (true? (executable/square-root? 4 2)))
  (is (true? (executable/square-root? 9 3)))
  (is (false? (executable/square-root? 5 2)))
  ;; Adaptive rate: base 1 over root 2 = 1/2 (accumulator 4).
  (is (= 1/2 (executable/rate 1 2)))
  (is (= 1/3 (executable/rate 1 3)))
  ;; A full scalar step: x=1, gradient=1, base rate 1, accumulator 4 (root 2):
  ;; x' = 1 - (1/2)*1 = 1/2.
  (is (= 1/2 (executable/adaptive-step 1 1 1 4))))
