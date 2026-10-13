(ns rainbow.algorithms.proofs.path-relaxation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.path-relaxation :as path]
            [rainbow.algorithms.reference.path-relaxation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          path/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest path-relaxation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (path/definition-ids checked-environment)
        theorems (path/theorem-ids checked-environment)]
    (is (= #{'path/relax} (set (keys definitions))))
    (is (= #{'path/relax-improves 'path/relax-keeps-current
             'path/relax-below-current 'path/relax-below-alt}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-path-relaxation-finds-shortest-distances
  (is (= 2 (executable/relax 7 2)))
  (is (= 2 (executable/relax 2 5)))
  (is (= 2 (executable/relax-all 7 [5 2 9])))
  ;; A tiny graph: 0->1 (4), 0->2 (1), 2->1 (1). Shortest 0->1 is via 2: 1+1=2.
  (let [dist (executable/bellman-ford [0 1 2]
                                      [[0 1 4] [0 2 1] [2 1 1]] 0)]
    (is (= 0 (dist 0)))
    (is (= 2 (dist 1)))
    (is (= 1 (dist 2)))))
