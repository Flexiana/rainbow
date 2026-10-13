(ns rainbow.math.finite.bellman-iterate-monotone-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-iterate-monotone :as iterate-monotone]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (iterate-monotone/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest value-below-optimality-iterate-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (iterate-monotone/definition-ids env)
                   (iterate-monotone/theorem-ids env))]
    (is (= #{'value/nnrat-value-below-optimality-iterate-zero
             'value/nnrat-value-below-optimality-iterate-successor
             'value/nnrat-value-below-optimality-iterate-rec
             'value/nnrat-value-below-optimality-iterate-generic
             'value/nnrat-value-below-optimality-iterate}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
