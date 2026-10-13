(ns rainbow.math.finite.bellman-signed-operator-fixed-point-convergence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-operator-fixed-point-convergence
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

(deftest signed-operator-fixed-point-convergence-is-axiom-free
  (let [env @checked-environment]
    (is (empty? (laws/definition-ids env)))
    (is (= #{'value/signed-operator-iterate-zero
             'value/signed-contractive-operator-fixed-point-additive-advance
             'value/signed-contractive-operator-iterate-fixed-point-additive-radius
             'value/signed-contractive-operator-iterate-fixed-point-converges-general-rate}
           (set (keys (laws/theorem-ids env)))))
    (doseq [[name id] (laws/theorem-ids env)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
