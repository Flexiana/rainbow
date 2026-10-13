(ns rainbow.algorithms.proofs.ahof.qp-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.qp :as qp]
            [rainbow.algorithms.reference.qp :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          qp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest qp-objective-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (qp/definition-ids checked-environment)
        theorems (qp/theorem-ids checked-environment)]
    (is (= #{'qp/objective} (set (keys definitions))))
    (is (= #{'qp/objective-unfold 'qp/objective-example 'qp/objective-at-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-qp-evaluates-and-minimizes
  (is (= 21 (executable/objective 2 3 1)))
  (is (= 0 (executable/objective 5 0 3)))
  ;; minimize x^2 - 4x: x* = 4/2 = 2 (c = -4, q = 1).
  (is (= 2 (executable/minimize-1d 1 -4)))
  (is (= -4 (executable/objective 1 2 -4))))
