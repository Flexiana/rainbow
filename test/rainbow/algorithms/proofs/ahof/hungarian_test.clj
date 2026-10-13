(ns rainbow.algorithms.proofs.ahof.hungarian-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.hungarian :as hungarian]
            [rainbow.algorithms.reference.hungarian :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          hungarian/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest hungarian-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (hungarian/definition-ids checked-environment)
        theorems (hungarian/theorem-ids checked-environment)]
    (is (= #{'hungarian/tight?} (set (keys definitions))))
    (is (= #{'hungarian/zero-reduced-cost-tight 'hungarian/tight-cost-zero
             'hungarian/positive-cost-not-tight}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-hungarian
  (is (true? (executable/tight? 0)))
  (is (false? (executable/tight? 3)))
  ;; classic 3x3 assignment: optimal cost 5 (rows [[4 1 3][2 0 5][3 2 2]])
  (is (= 5 (executable/min-cost-assignment [[4 1 3] [2 0 5] [3 2 2]])))
  ;; row reduction exposes a tight cell in each row
  (let [tight (executable/assignable-cells [[4 1 3] [2 0 5] [3 2 2]])]
    (is (contains? tight [0 1]))
    (is (contains? tight [1 1]))))
