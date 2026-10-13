(ns rainbow.algorithms.proofs.ahof.particle-filter-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.particle-filter :as pf]
            [rainbow.algorithms.reference.particle-filter :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pf/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest particle-filter-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pf/definition-ids checked-environment)
        theorems (pf/theorem-ids checked-environment)]
    (is (= #{'particle-filter/resamples?} (set (keys definitions))))
    (is (= #{'particle-filter/resamples-particle
             'particle-filter/resample-is-proportional
             'particle-filter/skips-below-draw}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-particle-filter-resamples
  ;; weights [1 3 2] -> cdf [1 4 6]
  (is (= [1 4 6] (executable/weight-cdf [1 3 2])))
  (is (= 1 (executable/resample-index [1 3 2] 4)))
  (is (= 0 (executable/resample-index [1 3 2] 1)))
  (is (= 2 (executable/resample-index [1 3 2] 5))))
