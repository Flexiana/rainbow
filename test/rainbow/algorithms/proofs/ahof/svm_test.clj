(ns rainbow.algorithms.proofs.ahof.svm-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.svm :as svm]
            [rainbow.algorithms.reference.svm :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          svm/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest svm-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (svm/definition-ids checked-environment)
        theorems (svm/theorem-ids checked-environment)]
    (is (= #{'svm/classify-positive?} (set (keys definitions))))
    (is (= #{'svm/positive-side-classified-positive
             'svm/confident-margin-at-least-one
             'svm/inside-margin-not-confident}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-svm
  (is (true? (executable/classify-positive? 2 0)))
  (is (false? (executable/classify-positive? 0 1)))
  ;; w=[1 0], b=0: points with x0>0 are positive
  (is (= 1 (executable/classify [1 0] 0 [3 5])))
  (is (= -1 (executable/classify [1 0] 0 [-2 5])))
  ;; a point exactly on the margin (w.x - b = 1) is a support vector
  (is (true? (executable/support-vector? [1 0] 0 [1 9] 1))))
