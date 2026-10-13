(ns rainbow.algorithms.proofs.ahof.falsification-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.falsification :as falsification]
            [rainbow.algorithms.reference.falsification :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          falsification/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest falsification-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (falsification/definition-ids checked-environment)
        theorems (falsification/theorem-ids checked-environment)]
    (is (= #{'falsification/falsifies?} (set (keys definitions))))
    (is (= #{'falsification/flags-counterexample
             'falsification/counterexample-is-sound
             'falsification/robust-not-flagged}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-falsification-finds-counterexamples
  (is (true? (executable/falsifies? 1 2)))
  (is (false? (executable/falsifies? 5 2)))
  ;; Robustness = |x - 5| (0 at the unsafe target 5); margin 1 flags x in [4,6].
  (let [robustness-of (fn [x] (max (- x 5) (- 5 x)))]
    (is (= 6 (executable/falsify robustness-of 1 [0 3 8 6 2])))
    (is (nil? (executable/falsify robustness-of 1 [0 3 8 2])))))
