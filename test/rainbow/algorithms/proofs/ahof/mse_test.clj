(ns rainbow.algorithms.proofs.ahof.mse-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.mse :as mse]
            [rainbow.algorithms.reference.mse :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mse/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest mse-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mse/definition-ids checked-environment)
        theorems (mse/theorem-ids checked-environment)]
    (is (= #{'mse/squared-error 'mse/mse} (set (keys definitions))))
    (is (= #{'mse/squared-error-example 'mse/mse-example
             'mse/perfect-fit-zero-loss}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-mse
  (is (= 9 (executable/squared-error 3)))
  (is (= 5/2 (executable/mse [2 1])))
  (is (= 0 (executable/mse [0 0 0])))
  ;; predictions [3 5] vs targets [2 3]: residuals [1 2], mse (1+4)/2 = 5/2
  (is (= 5/2 (executable/mse-predictions [3 5] [2 3]))))
