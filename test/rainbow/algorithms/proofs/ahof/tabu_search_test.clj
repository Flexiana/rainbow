(ns rainbow.algorithms.proofs.ahof.tabu-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.tabu-search :as tabu]
            [rainbow.algorithms.reference.tabu-search :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          tabu/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest tabu-search-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (tabu/definition-ids checked-environment)
        theorems (tabu/theorem-ids checked-environment)]
    (is (= #{'tabu-search/move-allowed?} (set (keys definitions))))
    (is (= #{'tabu-search/non-tabu-move-allowed 'tabu-search/tabu-move-forbidden}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-tabu-search
  (is (true? (executable/move-allowed? false)))
  (is (false? (executable/move-allowed? true)))
  ;; minimize (x-4)^2 over integers via +-1 moves; tabu list breaks cycles
  (let [neighbors (fn [x] [[(inc x) [:inc x]] [(dec x) [:dec x]]])
        best (executable/optimize #(* (- % 4) (- % 4)) neighbors 0 3 30)]
    (is (= 4 best))))
