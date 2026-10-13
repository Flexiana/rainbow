(ns rainbow.algorithms.proofs.ahof.min-max-scaling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.min-max-scaling :as mm]
            [rainbow.algorithms.reference.min-max-scaling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest min-max-scaling-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mm/definition-ids checked-environment)
        theorems (mm/theorem-ids checked-environment)]
    (is (= #{'min-max-scaling/scaled} (set (keys definitions))))
    (is (= #{'min-max-scaling/scaled-example 'min-max-scaling/maximum-maps-to-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-min-max-scaling
  (is (= 3/4 (executable/scaled 3 4)))
  (is (= 1 (executable/scaled 4 4)))
  ;; [2 4 6 10]: min 2, max 10, range 8 -> [0 1/4 1/2 1]
  (is (= [0 1/4 1/2 1] (executable/normalize [2 4 6 10]))))
