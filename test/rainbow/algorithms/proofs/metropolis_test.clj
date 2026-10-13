(ns rainbow.algorithms.proofs.metropolis-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.metropolis :as metropolis]
            [rainbow.algorithms.reference.metropolis :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          metropolis/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest metropolis-acceptance-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (metropolis/definition-ids checked-environment)
        theorems (metropolis/theorem-ids checked-environment)]
    (is (= #{'metropolis/accepts-downhill?} (set (keys definitions))))
    (is (= #{'metropolis/accepts-downhill-move
             'metropolis/downhill-does-not-worsen
             'metropolis/uphill-not-deterministic}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-metropolis-acceptance-matches-the-rule
  (is (true? (executable/accepts-downhill? 3 5)))
  (is (false? (executable/accepts-downhill? 8 5)))
  ;; Downhill always accepted regardless of the uniform draw.
  (is (executable/accept? 3 5 1.0 0.99))
  ;; Uphill at high temperature with a small uniform draw is accepted...
  (is (executable/accept? 6 5 100.0 0.1))
  ;; ...but a near-1 uniform draw rejects the same uphill move.
  (is (not (executable/accept? 6 5 0.5 0.999))))
