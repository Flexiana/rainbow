(ns rainbow.math.sets.fiber-characterization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.fiber-characterization :as characterization]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (characterization/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest image-injection-and-surjection-have-fiber-characterizations
  (let [checked-environment @checked-environment
        theorems (characterization/theorem-ids checked-environment)]
    (is (= #{'set/fiber-nonempty-of-image-member
             'set/image-member-of-fiber-nonempty
             'set/image-member-equivalent-fiber-nonempty
             'set/surjective-on-equivalent-nonempty-fibers
             'set/injective-on-equivalent-subsingleton-fibers}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
