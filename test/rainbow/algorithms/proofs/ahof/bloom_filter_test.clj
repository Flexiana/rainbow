(ns rainbow.algorithms.proofs.ahof.bloom-filter-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bloom-filter :as bloom]
            [rainbow.algorithms.reference.bloom-filter :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bloom/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bloom-filter-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bloom/definition-ids checked-environment)
        theorems (bloom/theorem-ids checked-environment)]
    (is (= #{'bloom-filter/possibly-present?} (set (keys definitions))))
    (is (= #{'bloom-filter/all-bits-set-possibly-present
             'bloom-filter/unset-first-bit-absent
             'bloom-filter/unset-second-bit-absent}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bloom-filter
  (is (true? (executable/possibly-present? true true)))
  (is (false? (executable/possibly-present? false true)))
  (let [bits (-> #{} (executable/add :a 3 64) (executable/add :b 3 64))]
    ;; no false negatives: added elements always test possibly-present
    (is (true? (executable/contains-maybe? bits :a 3 64)))
    (is (true? (executable/contains-maybe? bits :b 3 64)))
    ;; an element never added is (very likely) reported absent
    (is (false? (executable/contains-maybe? bits :zzz 3 64)))))
