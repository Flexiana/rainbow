(ns rainbow.algorithms.proofs.ahof.kkt-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.ahof.kkt :as kkt]
            [rainbow.algorithms.reference.kkt :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          kkt/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest kkt-stationarity-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (kkt/definition-ids checked-environment)
        theorems (kkt/theorem-ids checked-environment)]
    (is (= #{'kkt/stationarity} (set (keys definitions))))
    (is (= #{'kkt/stationarity-unfold
             'kkt/stationarity-example
             'kkt/stationarity-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-kkt-matches-and-checks-conditions
  (is (= [3 2] (executable/stationarity [0 0] 1 [3 2])))
  ;; A valid KKT point: gradF = -lambda*gradG makes stationarity zero, with
  ;; dual/primal feasibility and complementary slackness.
  (is (true? (executable/kkt-point? [-2 -2] 2 [1 1] 0)))
  ;; Non-stationary point fails.
  (is (false? (executable/kkt-point? [1 0] 1 [3 2] 0))))
