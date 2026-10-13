(ns rainbow.math.finite.markov-kernel-composition-positive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-kernel-composition-positive
             :as positive-compose]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (positive-compose/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest positive-intermediate-witnesses-positive-kernel-composition
  (let [env @checked-environment
        definitions (positive-compose/definition-ids env)
        theorems (positive-compose/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-compose-positive-of-member
             'markov/nnrat-kernel-compose-pointwise-positive}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
