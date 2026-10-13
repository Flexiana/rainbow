(ns rainbow.math.finite.policy-value-dominance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.policy-value-dominance :as dominance]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (dominance/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest policy-improvement-value-dominance-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (dominance/definition-ids env)
                   (dominance/theorem-ids env))]
    (is (= #{'value/nnrat-fixed-policy-step-monotone
             'value/nnrat-fixed-policy-post-fixed-below-sequence
             'value/nnrat-policy-improvement-value-dominates}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
