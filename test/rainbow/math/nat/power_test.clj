(ns rainbow.math.nat.power-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.power :as nat-power]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-power/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nat-power-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (nat-power/definition-ids checked-environment)
        theorems (nat-power/theorem-ids checked-environment)]
    (is (= #{'nat/power} (set (keys definitions))))
    (is (= #{'nat/power-step-unfold 'nat/power-zero 'nat/power-two-cubed
             'nat/power-three-squared 'nat/power-two-to-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
