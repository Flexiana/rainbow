(ns rainbow.algorithms.proofs.ahof.fenwick-tree-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.fenwick-tree :as ft]
            [rainbow.algorithms.reference.fenwick-tree :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ft/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fenwick-tree-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ft/definition-ids checked-environment)
        theorems (ft/theorem-ids checked-environment)]
    (is (= #{'fenwick-tree/accumulate} (set (keys definitions))))
    (is (= #{'fenwick-tree/accumulate-example
             'fenwick-tree/identity-node-unchanged}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-fenwick-tree
  (is (= 7 (executable/accumulate 3 4)))
  (is (= 5 (executable/accumulate 5 0)))
  (let [t (reduce (fn [t [i v]] (executable/update-point t i v))
                  (executable/build 6)
                  (map-indexed (fn [i v] [(inc i) v]) [1 2 3 4 5 6]))]
    (is (= 21 (executable/prefix-sum t 6)))
    (is (= 6 (executable/prefix-sum t 3)))
    (is (= 9 (executable/range-sum t 2 4)))
    ;; point update: add 10 at position 3, prefix sum grows by 10
    (let [t (executable/update-point t 3 10)]
      (is (= 31 (executable/prefix-sum t 6))))))
