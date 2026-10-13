(ns rainbow.algorithms.proofs.ahof.segment-tree-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.segment-tree :as st]
            [rainbow.algorithms.reference.segment-tree :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          st/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest segment-tree-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (st/definition-ids checked-environment)
        theorems (st/theorem-ids checked-environment)]
    (is (= #{'segment-tree/combine} (set (keys definitions))))
    (is (= #{'segment-tree/combine-example 'segment-tree/empty-segment-identity}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-segment-tree
  (is (= 7 (executable/combine 3 4)))
  (let [t (executable/build [1 2 3 4 5 6])]
    (is (= 21 (executable/range-sum t 0 6)))
    (is (= 9 (executable/range-sum t 1 4)))
    (is (= 5 (executable/range-sum t 4 5)))))
