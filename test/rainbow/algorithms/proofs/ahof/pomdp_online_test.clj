(ns rainbow.algorithms.proofs.ahof.pomdp-online-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pomdp-online :as po]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (po/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest pomdp-online-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (po/definition-ids env) (po/theorem-ids env))]
    (is (= #{'pomdp/perseus-backup 'pomdp/despot-lower 'pomdp/despot-upper
             'pomdp/freudenthal-interp 'pomdp/controller-node-value
             'pomdp/perseus-improves 'pomdp/despot-bracket
             'pomdp/freudenthal-within-corners 'pomdp/controller-node-value-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
