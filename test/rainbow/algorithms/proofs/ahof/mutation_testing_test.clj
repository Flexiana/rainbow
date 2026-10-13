(ns rainbow.algorithms.proofs.ahof.mutation-testing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.mutation-testing :as mutation]
            [rainbow.algorithms.reference.mutation-testing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mutation/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest mutation-testing-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mutation/definition-ids checked-environment)
        theorems (mutation/theorem-ids checked-environment)]
    (is (= #{'mutation/score 'mutation/adequate?} (set (keys definitions))))
    (is (= #{'mutation/score-example 'mutation/adequate-when-above
             'mutation/adequate-meets-threshold 'mutation/inadequate-when-below}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-mutation-testing
  (is (= 3/4 (executable/mutation-score 3 4)))
  (is (true? (executable/suite-adequate? 3 4 1/2)))
  (is (false? (executable/suite-adequate? 1 4 1/2))))
