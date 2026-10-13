(ns rainbow.algorithms.proofs.ahof.k2-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.k2 :as k2]
            [rainbow.algorithms.reference.k2 :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          k2/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest k2-improvement-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (k2/definition-ids checked-environment)
        theorems (k2/theorem-ids checked-environment)]
    (is (= #{'k2/improves?} (set (keys definitions))))
    (is (= #{'k2/accepts-improvement 'k2/accepted-does-not-decrease
             'k2/rejects-non-improvement}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-k2-greedily-adds-parents
  (is (true? (executable/improves? 8 5)))
  (is (false? (executable/improves? 4 5)))
  ;; Score improves with :a (10) but adding :b lowers it (8): keep {:a}.
  (let [score {#{} 5, #{:a} 10, #{:b} 6, #{:a :b} 8}]
    (is (= #{:a} (executable/best-parents [:a :b] score)))))
