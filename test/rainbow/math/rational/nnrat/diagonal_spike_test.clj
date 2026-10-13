(ns rainbow.math.rational.nnrat.diagonal-spike-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.diagonal-spike :as spike]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (spike/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest canonical-diagonal-spike-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (spike/definition-ids env)
        theorems (spike/theorem-ids env)]
    (is (= #{'finite/certified-equality-decision
             'finite/certified-exhaustive-carrier
             'finite/nnrat-diagonal-spike}
           (set (keys definitions))))
    (is (= #{'finite/certified-equality-of-exhaustive-carrier
             'finite/coverage-of-exhaustive-carrier
             'finite/nnrat-diagonal-spike-zero-of-different
             'finite/equality-decidable-of-certified-decision
             'finite/nnrat-diagonal-spike-mass-of-equal
             'finite/nnrat-diagonal-unit-spike-multiply
             'finite/nnrat-map-sum-diagonal-spike-zero-of-not-member
             'finite/nnrat-map-sum-diagonal-spike-of-member-no-duplicates
             'finite/nnrat-finset-diagonal-spike-total
             'finite/nnrat-finset-diagonal-spike-total-of-exhaustive-carrier}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
