(ns rainbow.math.rational.nnrat.metric-separation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.metric-separation :as separation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (separation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest nnrat-metric-separation-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (separation/definition-ids env)
        theorems (separation/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'nnrat/at-most-antisymmetric
             'nnrat/distance-at-most-zero-of-equivalent
             'nnrat/distance-zero-of-equivalent
             'nnrat/equivalent-of-distance-at-most-zero
             'nnrat/equivalent-of-distance-zero
             'nnrat/distance-zero-iff-equivalent
             'nnrat/distance-respects-equivalence
             'nnrat/distance-add-subadditive
             'nnrat/distance-multiply-left-bound
             'nnrat/map-sum-distance-bound
             'nnrat/map-sum-monotone-on
             'metric/finite-nnrat-sup-radius-zero-of-pointwise-equivalent
             'metric/pointwise-equivalent-of-finite-nnrat-sup-radius-zero
             'metric/finite-nnrat-sup-radius-zero-iff-pointwise-equivalent}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
