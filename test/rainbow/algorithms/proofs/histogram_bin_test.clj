(ns rainbow.algorithms.proofs.histogram-bin-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.histogram-bin :as histogram]
            [rainbow.algorithms.reference.histogram-bin :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          histogram/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest histogram-bin-count-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (histogram/definition-ids checked-environment)
        theorems (histogram/theorem-ids checked-environment)]
    (is (= #{'histogram/count-in-range} (set (keys definitions))))
    (is (= #{'histogram/cons-in-bin-increments
             'histogram/cons-below-bin-preserves
             'histogram/cons-above-bin-preserves
             'histogram/count-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-histogram-matches-the-counts
  (is (= 2 (executable/count-in-range 2 6 [1 4 7 5])))
  (is (= 0 (executable/count-in-range 2 6 [1 7 8])))
  ;; A three-bin histogram over edges [0 3 6 9].
  (is (= [2 2 1] (executable/histogram [0 3 6 9] [1 2 4 5 7])))
  ;; Boxcar density at 4 with width 2 over [1 4 7 5]: 2 of 4 within [2,6],
  ;; per unit width 2*2 -> 2/16 = 1/8.
  (is (= 1/8 (executable/density 4 2 [1 4 7 5]))))
