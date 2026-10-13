(ns rainbow.math.finite.markov-aperiodicity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-aperiodicity :as aperiodicity]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (aperiodicity/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gcd-free-aperiodicity-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (aperiodicity/definition-ids env)
        theorems (aperiodicity/theorem-ids env)]
    (is (= #{'markov/nnrat-aperiodic-at
             'markov/nnrat-aperiodic}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-aperiodic-at-of-return-at-one
             'markov/nnrat-aperiodic-of-all-return-at-one}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
