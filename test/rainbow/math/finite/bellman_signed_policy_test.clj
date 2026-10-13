(ns rainbow.math.finite.bellman-signed-policy-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-policy :as laws]))

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

(deftest signed-policy-bellman-certificates-are-native-and-axiom-free
  (let [env @checked-environment]
    (testing "one reducible Bellman bridge definition is installed"
      (is (= #{'bellman/signed-policy-step
               'bellman/signed-policy-iterate}
             (set (keys (laws/definition-ids env)))))
      (doseq [[name id] (laws/definition-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (testing "arbitrary signed rewards cancel from policy-step error"
      (is (= #{'bellman/signed-policy-step-reward-cancels-distance
               'bellman/signed-policy-step-general-rate-contraction
               'bellman/signed-policy-fixed-points-unique
               'bellman/signed-policy-fixed-point-residual-bound
               'bellman/signed-policy-fixed-point-stopping-certificate
               'bellman/signed-policy-iterate-error-exact-envelope
               'bellman/signed-policy-iterate-stopping-certificate
               'bellman/signed-policy-iterate-tail-bound
               'bellman/signed-policy-iterate-tail-stopping-certificate}
             (set (keys (laws/theorem-ids env)))))
      (doseq [[name id] (laws/theorem-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
