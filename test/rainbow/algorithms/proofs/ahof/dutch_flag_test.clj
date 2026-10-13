(ns rainbow.algorithms.proofs.ahof.dutch-flag-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.dutch-flag :as df]
            [rainbow.algorithms.reference.dutch-flag :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          df/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest dutch-flag-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (df/definition-ids checked-environment)
        theorems (df/theorem-ids checked-environment)]
    (is (= #{'dutch-flag/goes-low?} (set (keys definitions))))
    (is (= #{'dutch-flag/below-pivot-goes-low 'dutch-flag/low-element-below-pivot
             'dutch-flag/equal-element-stays-middle}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-dutch-flag
  (is (true? (executable/goes-low? 2 4)))
  (is (false? (executable/goes-low? 5 4)))
  ;; partition 0/1/2 values around pivot 1 -> all 0s, then 1s, then 2s
  (is (= [0 0 1 1 1 2 2] (executable/three-way-partition [2 0 1 2 1 0 1] 1))))
