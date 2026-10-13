(ns rainbow.math.rational.nnrat.contraction-uniqueness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.contraction-uniqueness :as cu]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (cu/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest contraction-collapse-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (cu/definition-ids env) (cu/theorem-ids env))]
    (is (= #{'nnrat/contraction-collapse} (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
