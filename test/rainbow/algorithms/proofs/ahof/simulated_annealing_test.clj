(ns rainbow.algorithms.proofs.ahof.simulated-annealing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.simulated-annealing :as sa]
            [rainbow.algorithms.reference.ahof-simulated-annealing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          sa/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest simulated-annealing-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (sa/definition-ids checked-environment)
        theorems (sa/theorem-ids checked-environment)]
    (is (= #{'simulated-annealing/accepts-uphill?} (set (keys definitions))))
    (is (= #{'simulated-annealing/accepts-worse-move
             'simulated-annealing/acceptance-within-probability
             'simulated-annealing/rejects-worse-move}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-simulated-annealing
  (is (true? (executable/accepts-uphill? 1/4 1/2)))
  (is (false? (executable/accepts-uphill? 3/4 1/2)))
  (is (true? (executable/accept? -2 1.0 0.9)))     ; downhill always accepted
  ;; minimize (x-3)^2 over integers, escaping to the minimum at x=3
  (let [best (executable/optimize #(* (- % 3) (- % 3))
                                  #(+ % (- (rand-int 3) 1))
                                  0 (repeat 500 1.0) (repeatedly 500 rand))]
    (is (<= (* (- best 3) (- best 3)) 1))))
