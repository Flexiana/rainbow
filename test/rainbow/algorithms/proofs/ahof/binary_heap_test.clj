(ns rainbow.algorithms.proofs.ahof.binary-heap-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.binary-heap :as heap]
            [rainbow.algorithms.reference.binary-heap :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          heap/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest binary-heap-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (heap/definition-ids checked-environment)
        theorems (heap/theorem-ids checked-environment)]
    (is (= #{'binary-heap/heap-ordered?} (set (keys definitions))))
    (is (= #{'binary-heap/parent-below-child-ordered
             'binary-heap/ordered-parent-at-most-child
             'binary-heap/parent-above-child-violates}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-binary-heap
  (is (true? (executable/heap-ordered? 2 5)))
  (is (false? (executable/heap-ordered? 7 3)))
  (is (= [1 1 2 3 4 5 5 6 9] (executable/heapsort [5 2 9 1 5 6 3 4 1]))))
