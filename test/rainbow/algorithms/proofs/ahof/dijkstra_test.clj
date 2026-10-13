(ns rainbow.algorithms.proofs.ahof.dijkstra-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.dijkstra :as dijkstra]
            [rainbow.algorithms.reference.dijkstra :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          dijkstra/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest dijkstra-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (dijkstra/definition-ids checked-environment)
        theorems (dijkstra/theorem-ids checked-environment)]
    (is (= #{'dijkstra/closer-vertex} (set (keys definitions))))
    (is (= #{'dijkstra/finalizes-closest 'dijkstra/finalizes-second-when-closer
             'dijkstra/finalized-is-closest}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-dijkstra
  (is (= 2 (executable/closer-vertex 3 2 8 5)))
  (is (= 5 (executable/closer-vertex 9 2 4 5)))
  ;; 0->1 (1), 1->2 (2), 0->2 (10): shortest 0->2 = 3
  (let [dist (executable/shortest-paths 3 {0 [[1 1] [2 10]] 1 [[2 2]] 2 []} 0)]
    (is (= 3 (dist 2)))
    (is (= 1 (dist 1)))))
