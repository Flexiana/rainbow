(ns rainbow.algorithms.proofs.prefix-sum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.prefix-sum :as prefix-sum]
            [rainbow.algorithms.reference.prefix-sum :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          prefix-sum/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest prefix-sum-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (prefix-sum/definition-ids checked-environment)
        theorems (prefix-sum/theorem-ids checked-environment)]
    (is (= #{'prefix-sum/scan-from 'prefix-sum/cumulative-sum}
           (set (keys definitions))))
    (is (= #{'prefix-sum/scan-cons 'prefix-sum/cumulative-sum-example
             'prefix-sum/cumulative-sum-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-prefix-sum-scans
  (is (= [1 3 6] (executable/cumulative-sum [1 2 3])))
  (is (= [] (executable/cumulative-sum [])))
  ;; CDF of [1/2 1/4 1/4] is [1/2 3/4 1].
  (is (= [1/2 3/4 1] (executable/cdf [1/2 1/4 1/4]))))
