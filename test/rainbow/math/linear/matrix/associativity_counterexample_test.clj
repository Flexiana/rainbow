(ns rainbow.math.linear.matrix.associativity-counterexample-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.matrix.associativity-counterexample :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest empty-middle-associativity-counterexample-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (laws/definition-ids env)
        theorems (laws/theorem-ids env)]
    (is (= #{'matrix/associativity-counterexample-left
             'matrix/associativity-counterexample-middle
             'matrix/associativity-counterexample-right}
           (set (keys definitions))))
    (is (= #{'matrix/associativity-counterexample-left-middle-composable
             'matrix/associativity-counterexample-middle-right-composable
             'matrix/associativity-counterexample-left-evaluates
             'matrix/associativity-counterexample-right-evaluates
             'matrix/associativity-counterexample-not-associative}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
