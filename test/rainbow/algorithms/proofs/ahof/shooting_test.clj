(ns rainbow.algorithms.proofs.ahof.shooting-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.shooting :as shooting]
            [rainbow.algorithms.reference.shooting :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          shooting/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest shooting-simulate-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (shooting/definition-ids checked-environment)
        theorems (shooting/theorem-ids checked-environment)]
    (is (= #{'shooting/simulate} (set (keys definitions))))
    (is (= #{'shooting/simulate-cons
             'shooting/simulate-empty
             'shooting/simulate-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-shooting-rolls-out-and-optimizes
  (is (= 6 (executable/simulate + 0 [1 2 3])))
  (is (= 0 (executable/simulate + 0 [])))
  ;; Over candidate plans, shooting picks the one whose final state is closest to
  ;; target 5 (additive dynamics from 0).
  (let [[plan state] (executable/shoot + 0 (fn [s] (max (- s 5) (- 5 s)))
                                       [[1 1] [2 3] [4 4]])]
    (is (= [2 3] plan))
    (is (= 5 state))))
