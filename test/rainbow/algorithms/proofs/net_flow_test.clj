(ns rainbow.algorithms.proofs.net-flow-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.net-flow :as net-flow]
            [rainbow.algorithms.reference.net-flow :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          net-flow/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest net-flow-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (net-flow/definition-ids checked-environment)
        theorems (net-flow/theorem-ids checked-environment)]
    (is (= #{'net-flow/net} (set (keys definitions))))
    (is (= #{'net-flow/net-unfold
             'net-flow/net-surplus-example
             'net-flow/net-larger-surplus-example
             'net-flow/net-surplus-nonnegative}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-net-flow-matches-the-balance
  (is (= 2 (executable/net 5 3)))
  (is (= 5 (executable/net 7 2)))
  (is (= -2 (executable/net 3 5)))
  (is (true? (executable/surplus? 5 3)))
  (is (false? (executable/surplus? 3 5)))
  ;; NPV of [10, 10] at discount 1/2 is 10 + 10*(1/2) = 15.
  (is (= 15 (executable/npv [10 10] 1/2))))
