(ns rainbow.algorithms.proofs.ahof.coin-change-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.coin-change :as coin]
            [rainbow.algorithms.reference.coin-change :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          coin/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest coin-change-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (coin/definition-ids checked-environment)
        theorems (coin/theorem-ids checked-environment)]
    (is (= #{'coin-change/cell} (set (keys definitions))))
    (is (= #{'coin-change/takes-cheaper-candidate 'coin-change/keeps-current-best
             'coin-change/at-most-candidate 'coin-change/at-most-current}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-coin-change
  (is (= 3 (executable/cell 5 3)))
  (is (= 4 (executable/cell 4 7)))
  ;; 11 from {1,2,5}: 5+5+1 = 3 coins
  (is (= 3 (executable/min-coins 11 [1 2 5])))
  (is (nil? (executable/min-coins 3 [2]))))
