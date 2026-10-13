(ns rainbow.math.nat.power-growth-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.add-order :as nat-add-order]
            [rainbow.math.nat.power :as nat-power]
            [rainbow.math.nat.power-growth :as nat-power-growth]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-add-order/extend-environment
          nat-power/extend-environment
          nat-power-growth/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest power-two-positivity-is-native-axiom-free
  (let [checked-environment @checked-environment
        theorems (nat-power-growth/theorem-ids checked-environment)]
    (is (= #{'nat/power-two-at-least-one 'nat/at-most-power-two
             'nat/le-multiply-succ}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
