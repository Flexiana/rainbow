(ns rainbow.algorithms.proofs.ahof.hypothesis-test-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.hypothesis-test :as ht]
            [rainbow.algorithms.reference.hypothesis-test :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ht/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hypothesis-test-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ht/definition-ids checked-environment)
        theorems (ht/theorem-ids checked-environment)]
    (is (= #{'hypothesis-test/reject-null?} (set (keys definitions))))
    (is (= #{'hypothesis-test/rejects-in-critical-region
             'hypothesis-test/rejection-meets-critical
             'hypothesis-test/fails-to-reject}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hypothesis-test
  (is (true? (executable/reject-null? 3 2)))
  (is (false? (executable/reject-null? 1 2)))
  ;; mean 105 vs mu0 100, sigma 15, n 36 -> z = 5/2.5 = 2 >= 1.96 -> reject
  (is (= :reject (executable/z-test 105 100 15 36 1.96)))
  (is (= :fail-to-reject (executable/z-test 101 100 15 36 1.96))))
