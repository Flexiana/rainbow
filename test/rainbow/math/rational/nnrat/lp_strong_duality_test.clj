(ns rainbow.math.rational.nnrat.lp-strong-duality-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.lp-strong-duality :as strong-duality]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (strong-duality/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest concrete-lp-strong-duality-is-native-axiom-free
  (let [env @checked-environment
        definitions (strong-duality/definition-ids env)
        theorems (strong-duality/theorem-ids env)
        ids (merge definitions theorems)]
    (is (= {} definitions))
    (is (= #{'nnrat/lp-example-strong-duality} (set (keys theorems))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name " is kernel-checked"))
      (is (= #{} (kernel/axioms env id)) (str name " is axiom-free")))))
