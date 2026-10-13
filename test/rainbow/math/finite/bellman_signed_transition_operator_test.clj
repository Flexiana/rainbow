(ns rainbow.math.finite.bellman-signed-transition-operator-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-transition-operator
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

(deftest named-signed-transition-bellman-interface-is-axiom-free
  (let [env @checked-environment]
    (testing "the concrete operator and iterate have stable reducible names"
      (is (= #{'value/nnrat-transition-signed-optimality-operator
               'value/signed-operator-iterate}
             (set (keys (laws/definition-ids env)))))
      (doseq [[name id] (laws/definition-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))
    (testing "opaque interface laws hide concrete transition expansion"
      (is (= #{'value/nnrat-transition-signed-optimality-operator-unfold
               'value/signed-operator-iterate-successor
               'value/signed-operator-iterate-successor-equivalent
               'value/signed-operator-successive-iterate-additive-radius
               'value/signed-contractive-operator-approximate-fixed-point-general-rate
               'value/nnrat-transition-signed-optimality-operator-additively-contractive}
             (set (keys (laws/theorem-ids env)))))
      (doseq [[name id] (laws/theorem-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
