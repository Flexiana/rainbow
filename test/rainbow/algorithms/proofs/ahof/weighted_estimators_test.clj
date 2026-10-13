(ns rainbow.algorithms.proofs.ahof.weighted-estimators-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.weighted-estimators :as we]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (we/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest weighted-estimators-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (we/definition-ids env) (we/theorem-ids env))]
    (is (= #{'est/mis-combine 'xai/ig-attribution-total 'opt/gauss-newton-hessian
             'opt/ridge-objective 'est/bayesian-mc-mean
             'est/mis-within-max 'xai/ig-completeness-example 'opt/gauss-newton-example
             'opt/ridge-example 'est/bayesian-mc-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
