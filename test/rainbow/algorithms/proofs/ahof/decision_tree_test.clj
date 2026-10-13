(ns rainbow.algorithms.proofs.ahof.decision-tree-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.decision-tree :as dtree]
            [rainbow.algorithms.reference.decision-tree :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          dtree/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest decision-tree-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (dtree/definition-ids checked-environment)
        theorems (dtree/theorem-ids checked-environment)]
    (is (= #{'decision-tree/choose-split 'decision-tree/is-leaf?}
           (set (keys definitions))))
    (is (= #{'decision-tree/picks-higher-gain 'decision-tree/chosen-gain-is-best
             'decision-tree/becomes-leaf 'decision-tree/keeps-splitting}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-decision-tree
  (is (= 1 (executable/choose-split 2 0 5 1)))
  (is (= 0 (executable/choose-split 5 0 2 1)))
  (is (true? (executable/is-leaf? 1 2)))
  (is (false? (executable/is-leaf? 5 2)))
  (is (= [3 7] (executable/best-split [[0 2] [3 7] [1 5]]))))
