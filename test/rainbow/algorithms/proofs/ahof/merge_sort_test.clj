(ns rainbow.algorithms.proofs.ahof.merge-sort-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.merge-sort :as ms]
            [rainbow.algorithms.reference.merge-sort :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ms/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest merge-sort-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ms/definition-ids checked-environment)
        theorems (ms/theorem-ids checked-environment)]
    (is (= #{'merge-sort/take-from-left?} (set (keys definitions))))
    (is (= #{'merge-sort/emits-smaller-left 'merge-sort/emitted-keeps-order
             'merge-sort/larger-left-yields}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-merge-sort
  (is (true? (executable/take-from-left? 2 5)))
  (is (false? (executable/take-from-left? 7 3)))
  (is (= [1 2 3 4] (executable/merge-runs [1 3] [2 4])))
  (is (= [1 1 2 3 4 5 5 6 9] (executable/merge-sort [5 2 9 1 5 6 3 4 1]))))
