(ns rainbow.algorithms.proofs.hypergradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.multiply :as signed-mul]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.algorithms.proofs.hypergradient :as hyper]
            [rainbow.algorithms.reference.hypergradient :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          signed-mul/extend-environment
          inner/extend-environment
          hyper/extend-environment))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest hypergradient-rate-update-is-native-axiom-free
  (let [env @checked-environment
        definitions (hyper/definition-ids env)
        theorems (hyper/theorem-ids env)]
    (is (= #{'hypergrad/update-rate} (set (keys definitions))))
    (is (= #{'hypergrad/update-rate-unfold 'hypergrad/aligned-example
             'hypergrad/orthogonal-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-hypergradient-tunes-rate-by-gradient-agreement
  ;; Aligned gradients grow the rate: 1 + 1*([1,1].[1,1]=2) = 3.
  (is (= 3 (executable/update-rate 1 1 [1 1] [1 1])))
  ;; Orthogonal gradients leave the rate unchanged.
  (is (= 2 (executable/update-rate 2 1 [1 0] [0 1])))
  ;; Anti-aligned gradients shrink the rate: 2 + 1*([1,0].[-1,0]=-1) = 1.
  (is (= 1 (executable/update-rate 2 1 [1 0] [-1 0]))))
