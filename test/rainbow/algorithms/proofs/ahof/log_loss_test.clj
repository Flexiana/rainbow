(ns rainbow.algorithms.proofs.ahof.log-loss-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.log-loss :as log-loss]
            [rainbow.algorithms.reference.log-loss :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          log-loss/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest log-loss-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (log-loss/definition-ids checked-environment)
        theorems (log-loss/theorem-ids checked-environment)]
    (is (= #{'log-loss/lower-loss?} (set (keys definitions))))
    (is (= #{'log-loss/confident-has-lower-loss
             'log-loss/lower-loss-more-probable
             'log-loss/unsure-not-lower-loss}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-log-loss
  (is (true? (executable/lower-loss? 3/4 1/4)))
  (is (false? (executable/lower-loss? 1/4 3/4)))
  ;; more-confident correct prediction has smaller loss
  (is (< (executable/log-loss 0.9) (executable/log-loss 0.6)))
  (is (< (abs (executable/log-loss 1.0)) 1e-9)))
