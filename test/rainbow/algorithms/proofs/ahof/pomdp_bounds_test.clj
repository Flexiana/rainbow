(ns rainbow.algorithms.proofs.ahof.pomdp-bounds-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pomdp-bounds :as pb]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (pb/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest pomdp-bounds-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (pb/definition-ids env) (pb/theorem-ids env))]
    (is (= #{'pomdp/belief-action-value 'pomdp/qmdp-value 'pomdp/blind-value
             'pomdp/fib-value 'pomdp/sawtooth-interp
             'pomdp/qmdp-dominates-action0 'pomdp/qmdp-dominates-action1
             'pomdp/blind-below-qmdp 'pomdp/fib-dominates-action0
             'pomdp/sawtooth-below-max-corner}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
