(ns rainbow.algorithms.proofs.ahof.pareto-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pareto :as pareto]
            [rainbow.algorithms.reference.pareto :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          pareto/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest pareto-dominance-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (pareto/definition-ids checked-environment)
        theorems (pareto/theorem-ids checked-environment)]
    (is (= #{'pareto/dominates?} (set (keys definitions))))
    (is (= #{'pareto/dominates-example
             'pareto/dominated-in-objective-1
             'pareto/dominated-in-objective-2
             'pareto/non-dominance-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-pareto-front-extraction
  (is (true? (executable/dominates? 2 3 5 4)))
  (is (false? (executable/dominates? 6 3 5 4)))
  ;; The dominated interior point [3 3] is filtered out of the front.
  (is (= [[1 4] [2 2] [4 1]]
         (executable/pareto-front [[1 4] [2 2] [4 1] [3 3]]))))
