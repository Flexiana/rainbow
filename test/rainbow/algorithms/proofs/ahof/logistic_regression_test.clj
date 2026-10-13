(ns rainbow.algorithms.proofs.ahof.logistic-regression-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.logistic-regression :as lr]
            [rainbow.algorithms.reference.logistic-regression :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          lr/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest logistic-regression-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lr/definition-ids checked-environment)
        theorems (lr/theorem-ids checked-environment)]
    (is (= #{'logistic/classify-positive?} (set (keys definitions))))
    (is (= #{'logistic/high-probability-positive
             'logistic/positive-meets-threshold
             'logistic/low-probability-negative}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-logistic-regression
  (is (true? (executable/classify-positive? 3/4 1/2)))
  (is (false? (executable/classify-positive? 1/4 1/2)))
  ;; learn threshold at x=0: y=1 for x>=1, y=0 for x<=-1
  (let [[w b] (executable/train 1 [[[2] 1] [[3] 1] [[-2] 0] [[-3] 0]] 0.5 200)]
    (is (= 1 (executable/classify w b [5])))
    (is (= 0 (executable/classify w b [-5])))))
