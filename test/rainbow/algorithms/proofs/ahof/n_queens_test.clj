(ns rainbow.algorithms.proofs.ahof.n-queens-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.n-queens :as nq]
            [rainbow.algorithms.reference.n-queens :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nq/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest n-queens-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (nq/definition-ids checked-environment)
        theorems (nq/theorem-ids checked-environment)]
    (is (= #{'n-queens/attacks-diagonally?} (set (keys definitions))))
    (is (= #{'n-queens/equal-distance-attacks 'n-queens/attack-distances-coincide
             'n-queens/unequal-distance-safe}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-n-queens
  (is (true? (executable/attacks-diagonally? 3 3)))
  (is (false? (executable/attacks-diagonally? 3 5)))
  ;; known solution counts
  (is (= 2 (executable/solve 4)))
  (is (= 10 (executable/solve 5)))
  (is (= 92 (executable/solve 8))))
