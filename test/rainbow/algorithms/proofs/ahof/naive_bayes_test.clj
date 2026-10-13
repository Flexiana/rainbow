(ns rainbow.algorithms.proofs.ahof.naive-bayes-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.naive-bayes :as nb]
            [rainbow.algorithms.reference.naive-bayes :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nb/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest naive-bayes-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (nb/definition-ids checked-environment)
        theorems (nb/theorem-ids checked-environment)]
    (is (= #{'naive-bayes/score 'naive-bayes/classify}
           (set (keys definitions))))
    (is (= #{'naive-bayes/score-example 'naive-bayes/classify-example
             'naive-bayes/prediction-dominates-one
             'naive-bayes/prediction-dominates-two}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-naive-bayes
  (is (= 6 (executable/nb-score 1 [2 3])))
  (is (= 0 (executable/classify [6 4 5])))
  ;; two classes: class0 prior 1/2 likes [1/2 1/2]=1/8; class1 prior 1/2 likes
  ;; [1/4 1/4]=1/32; class 0 wins
  (is (= 0 (executable/predict [[1/2 [1/2 1/2]] [1/2 [1/4 1/4]]]))))
