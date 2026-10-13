(ns rainbow.algorithms.proofs.ahof.softmax-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.softmax :as softmax]
            [rainbow.algorithms.reference.softmax :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          softmax/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest softmax-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (softmax/definition-ids checked-environment)
        theorems (softmax/theorem-ids checked-environment)]
    (is (= #{'softmax/share} (set (keys definitions))))
    (is (= #{'softmax/share-example 'softmax/shares-sum-to-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-softmax
  (is (= 3/4 (executable/softmax-share 3 4)))
  ;; softmax probabilities are non-negative and sum to 1
  (let [p (executable/softmax [1.0 2.0 3.0])]
    (is (every? pos? p))
    (is (< (abs (- 1.0 (reduce + p))) 1e-9))
    ;; largest score -> largest probability
    (is (= (apply max p) (last p)))))
