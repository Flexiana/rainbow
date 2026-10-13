(ns rainbow.math.finite.set-fiber-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-fiber :as fiber]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (fiber/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fibers-inside-finite-domains-are-constructively-finite
  (let [checked-environment @checked-environment
        definitions (fiber/definition-ids checked-environment)
        theorems (fiber/theorem-ids checked-environment)]
    (is (= #{'set/fiber-within}
           (set (keys definitions))))
    (is (= #{'set/fiber-within-subset
             'set/fiber-within-member-source
             'set/fiber-within-mapping-equals
             'set/finite-fiber-within}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
