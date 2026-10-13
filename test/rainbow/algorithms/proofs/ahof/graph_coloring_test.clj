(ns rainbow.algorithms.proofs.ahof.graph-coloring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.graph-coloring :as gc]
            [rainbow.algorithms.reference.graph-coloring :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest graph-coloring-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gc/definition-ids checked-environment)
        theorems (gc/theorem-ids checked-environment)]
    (is (= #{'graph-coloring/conflict?} (set (keys definitions))))
    (is (= #{'graph-coloring/same-color-conflicts
             'graph-coloring/conflict-colors-coincide
             'graph-coloring/different-colors-proper}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-graph-coloring
  (is (true? (executable/conflict? 2 2)))
  (is (false? (executable/conflict? 2 5)))
  ;; triangle needs 3 colors; the coloring is proper
  (let [adj {0 #{1 2} 1 #{0 2} 2 #{0 1}}
        colors (executable/greedy-color [0 1 2] adj)]
    (is (executable/proper? adj colors))
    (is (= 3 (count (set (vals colors))))))
  ;; bipartite path needs 2 colors
  (let [adj {0 #{1} 1 #{0 2} 2 #{1 3} 3 #{2}}
        colors (executable/greedy-color [0 1 2 3] adj)]
    (is (executable/proper? adj colors))))
