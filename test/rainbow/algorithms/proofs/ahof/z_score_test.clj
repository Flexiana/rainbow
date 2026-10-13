(ns rainbow.algorithms.proofs.ahof.z-score-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.z-score :as z]
            [rainbow.algorithms.reference.z-score :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          z/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest z-score-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (z/definition-ids checked-environment)
        theorems (z/theorem-ids checked-environment)]
    (is (= #{'z-score/z-score} (set (keys definitions))))
    (is (= #{'z-score/z-score-example 'z-score/one-sigma-z-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-z-score
  (is (= 3/2 (executable/z-score 3 2)))
  (is (= 1 (executable/z-score 2 2)))
  ;; data [2 4 4 4 5 5 7 9]: mean 5, sd 2; z of 9 is (9-5)/2 = 2
  (is (< (abs (- 2.0 (executable/standardize [2 4 4 4 5 5 7 9] 9))) 1e-9)))
