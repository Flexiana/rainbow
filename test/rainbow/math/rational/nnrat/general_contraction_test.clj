(ns rainbow.math.rational.nnrat.general-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.general-contraction :as gc]))
(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c)) (throw (ex-info "D63 rejected" {:c c})))
      (gc/extend-environment (:environment c)))))
(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) (set (:rainbow/universes d)))))))
(deftest general-contraction-step-axiom-free
  (let [env @checked-environment
        ids (merge (gc/definition-ids env) (gc/theorem-ids env))]
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
