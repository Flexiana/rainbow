(ns rainbow.math.finite.bellman-signed-policy-approximate-fixed-point-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-policy-approximate-fixed-point
             :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-policy-approximate-fixed-points-are-constructive-and-axiom-free
  (let [env @checked-environment
        theorems (laws/theorem-ids env)]
    (is (empty? (laws/definition-ids env)))
    (is (= #{'bellman/signed-policy-eventually-approximate-fixed-point
             'bellman/signed-policy-approximate-fixed-point-at-horizon
             'bellman/signed-policy-approximate-fixed-point-exists
             'bellman/signed-policy-successive-residual-rate-null-general
             'bellman/signed-policy-approximate-fixed-point-general-rate
             'bellman/signed-policy-approximate-fixed-point-exists-general-rate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
