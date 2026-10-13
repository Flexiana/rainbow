(ns rainbow.algorithms.proofs.floyd-warshall-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.floyd-warshall :as floyd-warshall]
            [rainbow.algorithms.reference.floyd-warshall :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          floyd-warshall/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest floyd-warshall-cell-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (floyd-warshall/definition-ids checked-environment)
        theorems (floyd-warshall/theorem-ids checked-environment)]
    (is (= #{'floyd-warshall/cell} (set (keys definitions))))
    (is (= #{'floyd-warshall/cell-relaxes
             'floyd-warshall/cell-below-direct
             'floyd-warshall/cell-below-detour}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-floyd-warshall-finds-all-pairs-shortest
  (is (= 7 (executable/cell 10 3 4)))
  ;; Graph 0->1 (10), 0->2 (3), 2->1 (4): shortest 0->1 is via 2 = 7.
  (let [dist (executable/all-pairs [0 1 2] {[0 1] 10, [0 2] 3, [2 1] 4})]
    (is (= 7 (dist [0 1])))
    (is (= 3 (dist [0 2])))
    (is (= 0 (dist [0 0])))))
