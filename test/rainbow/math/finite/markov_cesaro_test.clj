(ns rainbow.math.finite.markov-cesaro-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-cesaro :as cesaro]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (cesaro/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-cesaro-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (cesaro/definition-ids env)
        theorems (cesaro/theorem-ids env)]
    (is (= #{'markov/nnrat-cesaro-count
             'markov/nnrat-cesaro-sum
             'markov/nnrat-cesaro-average}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-cesaro-count-zero
             'markov/nnrat-cesaro-count-successor
             'markov/nnrat-cesaro-sum-zero
             'markov/nnrat-cesaro-sum-successor
             'markov/nnrat-cesaro-sum-total-mass
             'markov/nnrat-cesaro-average-normalized
             'markov/nnrat-stationary-cesaro-sum
             'markov/nnrat-stationary-cesaro-average}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
