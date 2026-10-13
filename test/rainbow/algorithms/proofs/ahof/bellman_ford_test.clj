(ns rainbow.algorithms.proofs.ahof.bellman-ford-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bellman-ford :as bf]
            [rainbow.algorithms.reference.bellman-ford :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bf/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bellman-ford-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bf/definition-ids checked-environment)
        theorems (bf/theorem-ids checked-environment)]
    (is (= #{'bellman-ford/relaxes?} (set (keys definitions))))
    (is (= #{'bellman-ford/shorter-path-relaxes
             'bellman-ford/update-decreases-distance
             'bellman-ford/no-improvement-rejected}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bellman-ford
  (is (true? (executable/relaxes? 3 5)))
  (is (false? (executable/relaxes? 7 5)))
  ;; 0->1 (2), 1->2 (3), 0->2 (10): shortest 0->2 is 5 via 1
  (is (= 5 ((executable/shortest-paths 3 [[0 1 2] [1 2 3] [0 2 10]] 0) 2))))
