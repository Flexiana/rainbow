(ns rainbow.algorithms.proofs.ahof.belief-propagation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.belief-propagation :as bp]
            [rainbow.algorithms.reference.belief-propagation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bp/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest belief-propagation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bp/definition-ids checked-environment)
        theorems (bp/theorem-ids checked-environment)]
    (is (= #{'belief-propagation/combine-messages} (set (keys definitions))))
    (is (= #{'belief-propagation/combine-messages-unfold
             'belief-propagation/combine-messages-example
             'belief-propagation/zero-message-annihilates}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-belief-propagation-multiplies-messages
  (is (= 12 (executable/combine-messages 3 4)))
  (is (= 0 (executable/combine-messages 0 7)))
  ;; Belief over 2 states from two incoming messages: [2 3] * [4 1] = [8 3];
  ;; normalized to [8/11 3/11].
  (is (= [8 3] (executable/belief [[2 3] [4 1]])))
  (is (= [8/11 3/11] (executable/normalize (executable/belief [[2 3] [4 1]])))))
