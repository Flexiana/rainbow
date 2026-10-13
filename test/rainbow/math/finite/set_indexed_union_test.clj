(ns rainbow.math.finite.set-indexed-union-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-indexed-union :as indexed-union]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (indexed-union/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-indexed-unions-are-constructive-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (indexed-union/definition-ids checked-environment)
        theorems (indexed-union/theorem-ids checked-environment)]
    (is (= #{'set/list-indexed-union
             'set/restricted-indexed-union}
           (set (keys definitions))))
    (is (= #{'set/restricted-indexed-union-member
             'set/list-indexed-union-member
             'set/finite-list-indexed-union
             'set/restricted-indexed-union-subset-list
             'set/finite-restricted-indexed-union
             'set/restricted-indexed-union-subset
             'set/indexed-union-subset-universal-restricted
             'set/finite-indexed-union}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
