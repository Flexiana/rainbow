(ns rainbow.algorithms.proofs.ahof.gas-station-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gas-station :as gs]
            [rainbow.algorithms.reference.gas-station :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          gs/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gas-station-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (gs/definition-ids checked-environment)
        theorems (gs/theorem-ids checked-environment)]
    (is (= #{'gas-station/can-complete?} (set (keys definitions))))
    (is (= #{'gas-station/sufficient-gas-completable
             'gas-station/completable-cost-covered
             'gas-station/gas-deficit-impossible}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-gas-station
  (is (true? (executable/can-complete? 7 5)))
  (is (false? (executable/can-complete? 3 5)))
  ;; classic: gas [1 2 3 4 5], cost [3 4 5 1 2] -> start at index 3
  (is (= 3 (executable/start-station [1 2 3 4 5] [3 4 5 1 2])))
  ;; deficit -> -1
  (is (= -1 (executable/start-station [2 3 4] [3 4 3]))))
