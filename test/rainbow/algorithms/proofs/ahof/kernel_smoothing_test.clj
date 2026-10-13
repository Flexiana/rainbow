(ns rainbow.algorithms.proofs.ahof.kernel-smoothing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kernel-smoothing :as ks]
            [rainbow.algorithms.reference.kernel-smoothing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ks/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kernel-smoothing-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ks/definition-ids checked-environment)
        theorems (ks/theorem-ids checked-environment)]
    (is (= #{'kernel-smoothing/weighted-sum 'kernel-smoothing/weight-total}
           (set (keys definitions))))
    (is (= #{'kernel-smoothing/weighted-sum-unfold
             'kernel-smoothing/weighted-sum-example
             'kernel-smoothing/weight-total-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kernel-smoothing-estimates
  (is (= 10 (executable/weighted-sum 2 3 1 4)))
  (is (= 3 (executable/weight-total 2 1)))
  (is (= 10/3 (executable/estimate [2 1] [3 4])))
  (is (= 5 (executable/estimate [1 1 2] [3 5 6]))))
