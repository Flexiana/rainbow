(ns rainbow.algorithms.proofs.ahof.kruskal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kruskal :as kruskal]
            [rainbow.algorithms.reference.kruskal :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kruskal/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kruskal-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kruskal/definition-ids checked-environment)
        theorems (kruskal/theorem-ids checked-environment)]
    (is (= #{'kruskal/accepts-edge?} (set (keys definitions))))
    (is (= #{'kruskal/adds-cross-component-edge 'kruskal/rejects-cycle-edge}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kruskal
  (is (true? (executable/accepts-edge? 3 5)))
  (is (false? (executable/accepts-edge? 3 3)))
  ;; triangle 0-1 (w1), 1-2 (w2), 0-2 (w3): MST takes the two cheapest
  (is (= [[1 0 1] [2 1 2]] (executable/mst 3 [[1 0 1] [2 1 2] [3 0 2]]))))
