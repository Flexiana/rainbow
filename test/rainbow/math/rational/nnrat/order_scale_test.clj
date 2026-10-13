(ns rainbow.math.rational.nnrat.order-scale-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.order-scale :as scale]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (scale/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest positive-order-scaling-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (scale/definition-ids env) (scale/theorem-ids env))]
    (is (= #{'nnrat/at-most-multiply-left-cancel
             'nnrat/multiply-divide-cancel
             'nnrat/at-most-multiply-left-normalize-upper
             'nnrat/at-most-multiply-left-normalize-lower
             'nnrat/zero-of-proper-contraction}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " kernel check"))
      (is (= #{} (kernel/axioms env id)) (str name " axioms")))))
