(ns rainbow.algorithms.proofs.ahof.cmaes-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.cmaes :as cmaes]
            [rainbow.algorithms.reference.cmaes :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          cmaes/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest cmaes-recombination-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (cmaes/definition-ids checked-environment)
        theorems (cmaes/theorem-ids checked-environment)]
    (is (= #{'cmaes/recombine} (set (keys definitions))))
    (is (= #{'cmaes/recombine-unfold
             'cmaes/recombine-top-example
             'cmaes/recombine-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-cmaes-recombines-elite
  (is (= [7 8] (executable/recombine-two 2 [3 2] 1 [1 4])))
  (is (= [3 2] (executable/recombine-two 1 [3 2] 0 [5 5])))
  ;; A convex combination of three elite with weights summing to 1.
  (is (= [2 2] (executable/recombine [1/2 1/4 1/4] [[2 0] [2 4] [2 4]]))))
