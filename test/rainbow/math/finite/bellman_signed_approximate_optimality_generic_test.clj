(ns rainbow.math.finite.bellman-signed-approximate-optimality-generic-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-approximate-optimality-generic
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

(deftest generic-signed-optimality-approximate-fixed-points-are-axiom-free
  (let [env @checked-environment
        theorems (laws/theorem-ids env)]
    (is (empty? (laws/definition-ids env)))
    (is (= #{'value/signed-optimality-successive-iterate-additive-radius
             'value/signed-optimality-approximate-fixed-point-general-rate
             'value/signed-optimality-approximate-fixed-point-exists-general-rate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
