(ns rainbow.algorithms.proofs.importance-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.importance-sampling :as ahof-d7]
            [rainbow.algorithms.proofs.importance-sampling :as iteration]
            [rainbow.algorithms.reference.importance-sampling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d11-bayesian-learning/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D11 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d7/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest importance-sampling-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'estimation/weighted-sum 'estimation/total-weight
             'estimation/importance-estimate}
           (set (keys definitions))))
    (is (= #{'estimation/weighted-sum-unfold
             'estimation/importance-estimate-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d7-importance-sampling-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d7/theorem-ids checked-environment)]
    (is (= #{'ahof-d7/weighted-sum-is-three
             'ahof-d7/total-weight-is-four
             'ahof-d7/estimate-is-three-quarters
             'ahof-d7/importance-sampling}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-importance-sampling-normalizes-by-total-weight
  ;; Unnormalized weights 3 and 1, values 1 and 0: the weighted sum is 3, the
  ;; total weight is 4, and the estimate is 3/4 -- normalizing by the total
  ;; weight, which is not 1.
  (is (= 3 (executable/weighted-sum 3 1 1 0)))
  (is (= 4 (executable/total-weight 3 1)))
  (is (= 3/4 (executable/importance-estimate 3 1 1 0)))
  ;; Weights that already sum to one leave the weighted sum unchanged.
  (is (= 3/4 (executable/importance-estimate 3/4 1 1/4 0))))
