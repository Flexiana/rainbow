(ns rainbow.math.finite.markov-expectation-invariance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-expectation-invariance :as invariance]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (invariance/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-expectation-invariance-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (invariance/definition-ids env)
        theorems (invariance/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'markov/nnrat-stationary-step-expectation-invariant
             'markov/nnrat-stationary-iterate-expectation-invariant
             'markov/nnrat-stationary-cesaro-expectation-invariant}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
