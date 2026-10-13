(ns rainbow.algorithms.proofs.ahof.precision-recall-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.precision-recall :as pr]
            [rainbow.algorithms.reference.precision-recall :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pr/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest precision-recall-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pr/definition-ids checked-environment)
        theorems (pr/theorem-ids checked-environment)]
    (is (= #{'precision-recall/precision 'precision-recall/recall}
           (set (keys definitions))))
    (is (= #{'precision-recall/precision-example 'precision-recall/recall-example
             'precision-recall/no-false-positives-precision-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-precision-recall
  (is (= 3/4 (executable/precision 3 1)))
  (is (= 3/5 (executable/recall 3 2)))
  (is (= 1 (executable/precision 5 0)))
  (is (= {:precision 4/5 :recall 2/3} (executable/from-confusion 8 2 4))))
