(ns rainbow.algorithms.proofs.counterfactual-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.math.rational.signed.multiply :as signed-mul]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.algorithms.proofs.counterfactual :as cf]
            [rainbow.algorithms.reference.counterfactual :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          signed-mul/extend-environment
          inner/extend-environment
          cf/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest counterfactual-distance-is-native-axiom-free
  (let [env @checked-environment
        definitions (cf/definition-ids env)
        theorems (cf/theorem-ids env)]
    (is (= #{'counterfactual/distance-squared} (set (keys definitions))))
    (is (= #{'counterfactual/distance-example 'counterfactual/closer-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-counterfactual-measures-proximity-exactly
  ;; (4-1)^2 + 0 = 9.
  (is (= 9 (executable/distance-squared [4 0] [1 0])))
  ;; (4-3)^2 + (5-4)^2 = 2.
  (is (= 2 (executable/distance-squared [4 5] [3 4])))
  ;; A candidate equal to the original has zero distance.
  (is (= 0 (executable/distance-squared [2 3] [2 3])))
  ;; Full score with a class penalty: distance 2 + 3*1 = 5.
  (is (= 5 (executable/score [4 5] [3 4] 3 1))))
