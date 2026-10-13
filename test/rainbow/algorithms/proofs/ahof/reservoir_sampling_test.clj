(ns rainbow.algorithms.proofs.ahof.reservoir-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.reservoir-sampling :as rs]
            [rainbow.algorithms.reference.reservoir-sampling :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          rs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest reservoir-sampling-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (rs/definition-ids checked-environment)
        theorems (rs/theorem-ids checked-environment)]
    (is (= #{'reservoir-sampling/replaces?} (set (keys definitions))))
    (is (= #{'reservoir-sampling/slot-in-reservoir-replaces
             'reservoir-sampling/replacement-within-reservoir
             'reservoir-sampling/slot-beyond-reservoir-discards}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reservoir-sampling
  (is (true? (executable/replaces? 2 3)))
  (is (false? (executable/replaces? 5 3)))
  ;; k=2, stream [10 20 30 40], rng always draws slot 1 -> replaces slot 0
  (is (= [40 20] (executable/sample 2 [10 20 30 40] (fn [_] 1))))
  ;; rng always draws slot beyond k -> reservoir keeps the first k
  (is (= [10 20] (executable/sample 2 [10 20 30 40] (fn [i] i)))))
