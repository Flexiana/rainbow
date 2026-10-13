(ns rainbow.algorithms.proofs.triangular-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.triangular :as triangular]
            [rainbow.algorithms.reference.triangular :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          triangular/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest triangular-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (triangular/definition-ids checked-environment)
        theorems (triangular/theorem-ids checked-environment)]
    (is (= #{'triangular/number} (set (keys definitions))))
    (is (= #{'triangular/step-unfold 'triangular/number-zero
             'triangular/number-four 'triangular/number-five}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-triangular-matches-and-agrees-with-closed-form
  (is (= 0 (executable/number 0)))
  (is (= 10 (executable/number 4)))
  (is (= 15 (executable/number 5)))
  ;; The recurrence sum and Gauss's closed form agree over a range.
  (is (= (mapv executable/number (range 10))
         (mapv executable/closed-form (range 10)))))
