(ns rainbow.algorithms.proofs.ahof.f1-score-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.f1-score :as f1]
            [rainbow.algorithms.reference.f1-score :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          f1/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest f1-score-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (f1/definition-ids checked-environment)
        theorems (f1/theorem-ids checked-environment)]
    (is (= #{'f1-score/f1} (set (keys definitions))))
    (is (= #{'f1-score/f1-example 'f1-score/perfect-classifier-f1-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-f1-score
  (is (= 3/5 (executable/f1 3/4 1/2)))
  (is (= 1 (executable/f1 1 1)))
  ;; TP=8, FP=2, FN=2: precision 4/5, recall 4/5, F1 4/5
  (is (= 4/5 (executable/f1-from-confusion 8 2 2))))
