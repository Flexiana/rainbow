(ns rainbow.math.finite.bellman-signed-value-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-value-iteration
             :as value-iteration]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (value-iteration/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-bellman-signed-value-iteration-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (value-iteration/definition-ids env)
        theorems (value-iteration/theorem-ids env)]
    (is (= #{'value/signed-iterate
             'value/signed-vi-error-radius}
           (set (keys definitions))))
    (is (= #{'value/signed-iterate-zero
             'value/signed-iterate-successor
             'value/signed-iterate-additive-radius
             'value/nnrat-transition-signed-step-fixed-point-contraction
             'value/nnrat-transition-signed-iterate-fixed-point-additive-radius}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
