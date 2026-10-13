(ns rainbow.algorithms.proofs.ahof.bayesian-optimization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bayesian-optimization :as bayesopt]
            [rainbow.algorithms.reference.bayesian-optimization :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bayesopt/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bayesopt-incumbent-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bayesopt/definition-ids checked-environment)
        theorems (bayesopt/theorem-ids checked-environment)]
    (is (= #{'bayesopt/update-incumbent} (set (keys definitions))))
    (is (= #{'bayesopt/adopts-better-candidate
             'bayesopt/incumbent-never-regresses
             'bayesopt/incumbent-dominates-candidate}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bayesian-optimization-tracks-best
  (is (= 8 (executable/update-incumbent 5 8)))
  (is (= 5 (executable/update-incumbent 5 3)))
  ;; Maximize f(x) = 10 - (x-4)^2 by proposing the grid around the best so far.
  (let [f (fn [x] (- 10 (* (- x 4) (- x 4))))
        select (fn [obs] (inc (first (apply max-key second obs))))
        best (executable/optimize select f [0] 6)]
    (is (= 10 best))))
