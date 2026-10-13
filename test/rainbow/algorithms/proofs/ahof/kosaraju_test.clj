(ns rainbow.algorithms.proofs.ahof.kosaraju-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.kosaraju :as kos]
            [rainbow.algorithms.reference.kosaraju :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          kos/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kosaraju-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kos/definition-ids checked-environment)
        theorems (kos/theorem-ids checked-environment)]
    (is (= #{'kosaraju/same-scc?} (set (keys definitions))))
    (is (= #{'kosaraju/mutual-reach-same-scc
             'kosaraju/forward-unreachable-different
             'kosaraju/backward-unreachable-different}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kosaraju
  (is (true? (executable/same-scc? true true)))
  (is (false? (executable/same-scc? false true)))
  ;; 0<->1 cycle, 2->3->2 cycle, 1->2 bridge: two SCCs {0 1} and {2 3}
  (let [adj {0 #{1} 1 #{0 2} 2 #{3} 3 #{2}}
        comps (executable/sccs [0 1 2 3] adj)]
    (is (= 2 (count comps)))
    (is (contains? comps #{0 1}))
    (is (contains? comps #{2 3}))))
