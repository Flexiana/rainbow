(ns rainbow.math.rational.nnrat.lp-separable-two-var-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.lp-separable-two-var :as separable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (separable/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest separable-two-var-zero-gap-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (separable/definition-ids env)
        theorems (separable/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= {} definitions))
    (is (= #{'nnrat/lp-separable-two-var-zero-gap}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " is kernel-checked"))
      (is (= #{} (kernel/axioms env id)) (str name " is axiom-free")))))
