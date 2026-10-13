(ns rainbow.math.rational.nnrat.harmonic-convergence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.harmonic-convergence :as hc]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (hc/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest harmonic-convergence-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (hc/definition-ids env) (hc/theorem-ids env))]
    (is (= #{'analysis/rate-null 'nnrat/harmonic 'nat/successor-monotone
             'analysis/harmonic-rate-null 'analysis/rate-null-dominated}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
