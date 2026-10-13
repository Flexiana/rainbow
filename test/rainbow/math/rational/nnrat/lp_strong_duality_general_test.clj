(ns rainbow.math.rational.nnrat.lp-strong-duality-general-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.lp-strong-duality-general :as general]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (general/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest scalar-strong-duality-generalization-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (general/definition-ids env)
        theorems (general/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= {} definitions))
    (is (= #{'nnrat/lp-single-constraint-weak-duality
             'nnrat/lp-single-constraint-optimality-certificate
             'nnrat/lp-single-constraint-dual-optimality-certificate
             'nnrat/lp-single-positive-constraint-dual-match-encodes
             'nnrat/lp-single-positive-constraint-dual-match-extracts
             'nnrat/lp-single-positive-constraint-dual-match-encoding-iff
             'nnrat/lp-single-positive-constraint-strong-duality-or-farkas-certificate
             'nnrat/lp-single-positive-constraint-strong-duality}
           (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " is kernel-checked"))
      (is (= #{} (kernel/axioms env id)) (str name " is axiom-free")))))
