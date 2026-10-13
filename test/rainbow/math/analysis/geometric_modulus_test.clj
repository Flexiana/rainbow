(ns rainbow.math.analysis.geometric-modulus-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.add-order :as nat-add-order]
            [rainbow.math.logic.half-monotone :as half-monotone]
            [rainbow.math.analysis.geometric-sequence :as geometric-sequence]
            [rainbow.math.nat.power :as nat-power]
            [rainbow.math.nat.distributive :as nat-distributive]
            [rainbow.math.nat.power-growth :as nat-power-growth]
            [rainbow.math.analysis.geometric-denominator :as geometric-denominator]
            [rainbow.math.analysis.geometric-modulus :as geometric-modulus]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-add-order/extend-environment
          half-monotone/extend-environment
          geometric-sequence/extend-environment
          nat-power/extend-environment
          nat-distributive/extend-environment
          nat-power-growth/extend-environment
          geometric-denominator/extend-environment
          geometric-modulus/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest geometric-modulus-is-native-axiom-free
  (let [checked-environment @checked-environment
        theorems (geometric-modulus/theorem-ids checked-environment)]
    (is (= #{'geometric/reaches-below-epsilon
             'geometric/converges-for-positive-epsilon}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
