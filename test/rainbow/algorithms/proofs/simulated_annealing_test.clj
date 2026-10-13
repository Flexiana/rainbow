(ns rainbow.algorithms.proofs.simulated-annealing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.simulated-annealing :as annealing]
            [rainbow.algorithms.reference.simulated-annealing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (annealing/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest simulated-annealing-schedule-and-acceptance-are-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (annealing/definition-ids checked-environment)
        theorems (annealing/theorem-ids checked-environment)]
    (is (= #{'annealing/cool 'annealing/accept-better?}
           (set (keys definitions))))
    (is (= #{'annealing/cool-unfold 'annealing/accept-unfold
             'annealing/accept-better-example 'annealing/reject-worse-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-simulated-annealing-cools-and-accepts-exactly
  ;; Geometric cooling over exact rationals.
  (is (= 1/2 (executable/cool 1/2 1)))
  (is (= 1/4 (executable/cool 1/2 (executable/cool 1/2 1))))
  ;; Greedy-limit acceptance.
  (is (true? (executable/accept-better? 1 2)))
  (is (false? (executable/accept-better? 2 1)))
  (is (true? (executable/accept-better? 3 3)))
  ;; Full Metropolis: uphill move accepted only when the draw beats the threshold.
  (is (true? (executable/metropolis-accept? 5 3 1/2 1/4)))
  (is (false? (executable/metropolis-accept? 5 3 1/2 3/4)))
  ;; One greedy step keeps the cheaper state and cools.
  (let [cost (fn [x] (* x x))
        result (executable/step cost 3 -1 1 1/2)]
    (is (= -1 (:state result)))
    (is (= 1/2 (:temperature result)))))
