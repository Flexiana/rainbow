(ns rainbow.math.analysis.geometric-sequence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.add-order :as nat-add-order]
            [rainbow.math.logic.half-monotone :as half-monotone]
            [rainbow.math.analysis.geometric-sequence :as geometric-sequence]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-add-order/extend-environment
          half-monotone/extend-environment
          geometric-sequence/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest geometric-sequence-monotonicity-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (geometric-sequence/definition-ids checked-environment)
        theorems (geometric-sequence/theorem-ids checked-environment)]
    (is (= #{'geometric/seq} (set (keys definitions))))
    (is (= #{'geometric/seq-step-unfold 'geometric/seq-step-monotone
             'geometric/seq-decreases-with-iteration
             'geometric/seq-numerator-invariant}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
