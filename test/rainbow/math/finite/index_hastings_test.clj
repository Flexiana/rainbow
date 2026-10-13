(ns rainbow.math.finite.index-hastings-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.index-hastings :as instantiation]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (instantiation/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest the-canonical-kernel-is-stationary-on-every-finite-index-space
  (testing "no abstract carrier, no supplied placement, no equality or coverage
            hypothesis: for every bound n and every normalized target and
            proposal over Index n, stationarity -- fully instantiated, checked,
            axiom-free"
    (let [env @checked-environment
          ids (instantiation/theorem-ids env)]
      (is (= #{'finite/index-certified-equality-decision
               'finite/index-certified-exhaustive-carrier
               'mcmc/nnrat-hastings-index-canonical-kernel-stationary}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
