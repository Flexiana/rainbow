(ns rainbow.algorithms.proofs.ahof.topological-sort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.topological-sort :as topo]
            [rainbow.algorithms.reference.topological-sort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          topo/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest topological-sort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (topo/definition-ids checked-environment)
        theorems (topo/theorem-ids checked-environment)]
    (is (= #{'topological-sort/ready?} (set (keys definitions))))
    (is (= #{'topological-sort/no-prerequisites-ready
             'topological-sort/has-prerequisites-not-ready
             'topological-sort/ready-in-degree-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-topological-sort
  (is (true? (executable/ready? 0)))
  (is (false? (executable/ready? 2)))
  ;; 0->1->2, 0->2 : valid order starts at 0, ends at 2
  (let [order (executable/topological-sort [0 1 2] {0 [1 2] 1 [2] 2 []})]
    (is (= 0 (first order)))
    (is (= 2 (last order)))
    (is (= 3 (count order)))))
