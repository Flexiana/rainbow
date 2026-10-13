(ns rainbow.math.sets.range-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.finset-powersets :as finset-powersets]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.range :as set-range]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint finset-powersets/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-85 checkpoint rejected" {:checkpoint checkpoint})))
      (set-range/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest lean-range-wrapper-is-reducible-axiom-free-data
  (let [checked-environment @checked-environment
        id (get (set-range/definition-ids checked-environment)
                'set/lean-range)
        declaration (environment/declaration checked-environment id)]
    (is (= :definition (:rainbow/kind declaration)))
    (is (= :reducible (:rainbow/transparency declaration)))
    (is (= #{} (kernel/axioms checked-environment id)))
    (is (kernel-checked? checked-environment id))))

(deftest finite-range-constant-is-axiom-free-proof-data
  (let [checked-environment @checked-environment
        id (get (set-range/theorem-ids checked-environment)
                'set/finite-range-constant)]
    (is (= #{} (kernel/axioms checked-environment id)))
    (is (kernel-checked? checked-environment id))))
