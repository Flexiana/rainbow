(ns rainbow.math.rational.nnrat.geometric-convergence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.geometric-convergence :as gc]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (gc/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest geometric-convergence-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (gc/definition-ids env) (gc/theorem-ids env))]
    (is (= #{'nat/pow2-pred 'nnrat/geometric-half
             'nat/index-le-pow2-pred 'analysis/geometric-below-harmonic
             'analysis/geometric-half-rate-null 'analysis/geometric-error-converges}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
