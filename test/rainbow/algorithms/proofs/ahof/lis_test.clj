(ns rainbow.algorithms.proofs.ahof.lis-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.lis :as lis]
            [rainbow.algorithms.reference.lis :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lis/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest lis-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lis/definition-ids checked-environment)
        theorems (lis/theorem-ids checked-environment)]
    (is (= #{'lis/extends?} (set (keys definitions))))
    (is (= #{'lis/element-extends-run 'lis/extension-keeps-increasing
             'lis/smaller-element-cannot-extend}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-lis
  (is (true? (executable/extends? 5 7)))
  (is (false? (executable/extends? 5 3)))
  ;; classic [10 9 2 5 3 7 101 18] -> LIS length 4 (e.g. 2 3 7 101)
  (is (= 4 (executable/lis-length [10 9 2 5 3 7 101 18])))
  (is (= 1 (executable/lis-length [5 4 3 2 1]))))
