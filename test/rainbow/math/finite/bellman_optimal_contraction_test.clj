(ns rainbow.math.finite.bellman-optimal-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-optimal-contraction :as contraction]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (contraction/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-argmax-and-optimality-step-are-additively-nonexpansive
  (let [env @checked-environment
        ids (contraction/theorem-ids env)]
    (is (= #{'decision/finite-nnrat-argmax-additive-upper-bound
             'decision/finite-nnrat-argmax-additively-nonexpansive
             'value/nnrat-optimality-step-additive-upper-bound
             'value/nnrat-optimality-step-additively-nonexpansive}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
