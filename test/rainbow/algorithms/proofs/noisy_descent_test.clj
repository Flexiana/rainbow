(ns rainbow.algorithms.proofs.noisy-descent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.noisy-descent :as noisy]
            [rainbow.algorithms.reference.noisy-descent :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint) vector/extend-environment
          noisy/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest noisy-descent-wrap-is-native-axiom-free
  (let [env @checked-environment
        definitions (noisy/definition-ids env)
        theorems (noisy/theorem-ids env)]
    (is (= #{'noisy/wrap} (set (keys definitions))))
    (is (= #{'noisy/wrap-unfold 'noisy/wrap-example 'noisy/wrap-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-noisy-descent-perturbs-exactly
  (is (= [2 3] (executable/wrap [1 2] [1 1])))
  (is (= [2 3 4] (executable/wrap [1 2 3] [1 1 1])))
  ;; Full noisy step: x=[0,0], gradient=[1,2], rate=1, noise=[2,3]:
  ;; (x - 1*grad) + noise = [-1,-2] + [2,3] = [1,1].
  (is (= [1 1] (executable/noisy-descent-step [0 0] [1 2] 1 [2 3]))))
