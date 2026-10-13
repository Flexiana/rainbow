(ns rainbow.algorithms.proofs.ahof.quicksort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.quicksort :as qs]
            [rainbow.algorithms.reference.quicksort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          qs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest quicksort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (qs/definition-ids checked-environment)
        theorems (qs/theorem-ids checked-environment)]
    (is (= #{'quicksort/goes-left?} (set (keys definitions))))
    (is (= #{'quicksort/small-goes-left 'quicksort/left-partition-below-pivot
             'quicksort/large-goes-right}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-quicksort
  (is (true? (executable/goes-left? 3 5)))
  (is (false? (executable/goes-left? 8 5)))
  (is (= [1 1 2 3 4 5 5 6 9] (executable/quicksort [5 2 9 1 5 6 3 4 1])))
  (is (= [] (executable/quicksort []))))
