(ns rainbow.algorithms.proofs.rmsprop-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.rmsprop :as rmsprop]
            [rainbow.algorithms.reference.rmsprop :as executable]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (rmsprop/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest rmsprop-accumulator-is-native-axiom-free
  (let [env @checked-environment
        definitions (rmsprop/definition-ids env)
        theorems (rmsprop/theorem-ids env)]
    (is (= #{'rmsprop/accumulate} (set (keys definitions))))
    (is (= #{'rmsprop/accumulate-unfold 'rmsprop/steady-state-example
             'rmsprop/rising-example} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))

(deftest executable-rmsprop-decays-accumulator-exactly
  ;; Steady state: 1/2*4 + 1/2*4 = 4.
  (is (= 4 (executable/accumulate 1/2 1/2 4 4)))
  ;; Rising: 1/2*4 + 1/2*16 = 10.
  (is (= 10 (executable/accumulate 1/2 1/2 4 16)))
  ;; Adaptive rate on a perfect-square accumulator: 1/sqrt(4) = 1/2.
  (is (= 1/2 (executable/rate 1 4)))
  (is (= 1/3 (executable/rate 1 9))))
