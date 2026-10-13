(ns rainbow.math.finite.markov-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-iteration :as iteration]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (iteration/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-iteration-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (iteration/definition-ids env)
        theorems (iteration/theorem-ids env)]
    (is (= #{'markov/nnrat-kernel-iterate}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-iterate-zero
             'markov/nnrat-kernel-iterate-successor
             'markov/nnrat-kernel-iterate-respects-mass-equivalence
             'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence
             'markov/nnrat-kernel-iterate-preserves-normalization
             'markov/nnrat-stationary-kernel-iterate}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
