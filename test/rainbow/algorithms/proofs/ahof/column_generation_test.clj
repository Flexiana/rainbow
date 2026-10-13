(ns rainbow.algorithms.proofs.ahof.column-generation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.column-generation :as colgen]
            [rainbow.algorithms.reference.column-generation :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          colgen/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest column-generation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (colgen/definition-ids checked-environment)
        theorems (colgen/theorem-ids checked-environment)]
    (is (= #{'column-generation/worth-adding?} (set (keys definitions))))
    (is (= #{'column-generation/prices-favorably
             'column-generation/added-column-improves
             'column-generation/pricing-converged}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-column-generation-prices
  (is (true? (executable/worth-adding? 3 5)))
  (is (false? (executable/worth-adding? 7 5)))
  (is (= [[3 5]] (executable/price-columns [[3 5] [7 5] [8 6]])))
  (is (true? (executable/optimal? [[7 5] [8 6]]))))
