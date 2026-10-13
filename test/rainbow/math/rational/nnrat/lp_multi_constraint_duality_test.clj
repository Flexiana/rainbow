(ns rainbow.math.rational.nnrat.lp-multi-constraint-duality-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.lp-multi-constraint-duality :as multi]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (multi/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-positive-multi-constraint-duality-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (multi/definition-ids env)
        theorems (multi/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= #{'nnrat/lp-positive-constraint-ratios
             'nnrat/lp-positive-constraints-feasible}
           (set (keys definitions))))
    (is (= #{'nnrat/lp-positive-constraints-normalize-upper
             'nnrat/lp-positive-multi-primal-feasible
             'nnrat/lp-positive-multi-primal-largest
             'nnrat/lp-positive-multi-primal-optimal
             'nnrat/lp-positive-multi-head-binding-strong-duality}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " is kernel-checked"))
      (is (= #{} (kernel/axioms env id)) (str name " is axiom-free")))))
