(ns rainbow.algorithms.proofs.ahof.perceptron-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.perceptron :as perceptron]
            [rainbow.algorithms.reference.perceptron :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          perceptron/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest perceptron-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (perceptron/definition-ids checked-environment)
        theorems (perceptron/theorem-ids checked-environment)]
    (is (= #{'perceptron/fires?} (set (keys definitions))))
    (is (= #{'perceptron/activation-fires 'perceptron/firing-meets-threshold
             'perceptron/subthreshold-does-not-fire}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-perceptron
  (is (true? (executable/fires? 3 2)))
  (is (false? (executable/fires? 1 2)))
  ;; learn AND: examples with 2 features
  (let [[w b] (executable/train 2 [[[0 0] 0] [[0 1] 0] [[1 0] 0] [[1 1] 1]] 20)]
    (is (= 1 (executable/predict w b [1 1])))
    (is (= 0 (executable/predict w b [0 1])))))
