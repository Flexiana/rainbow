(ns rainbow.math.sets.fiber-unique-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.fiber-unique :as fiber-unique]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (fiber-unique/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest unique-existence-and-bijection-fibers-are-constructive
  (let [checked-environment @checked-environment
        theorems (fiber-unique/theorem-ids checked-environment)]
    (is (= #{'proposition/unique-existence-of-existence-and-subsingleton
             'proposition/existence-and-subsingleton-of-unique-existence
             'proposition/unique-existence-equivalent-existence-and-subsingleton
             'set/bijective-on-has-unique-fibers
             'set/bijective-on-equivalent-maps-to-and-unique-fibers}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
