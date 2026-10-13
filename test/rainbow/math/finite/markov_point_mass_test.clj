(ns rainbow.math.finite.markov-point-mass-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-point-mass :as point-mass]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (point-mass/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest canonical-point-mass-selects-a-kernel-row
  (let [env @checked-environment
        definitions (point-mass/definition-ids env)
        theorems (point-mass/theorem-ids env)]
    (is (= #{'markov/nnrat-point-mass}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-point-mass-positive-at-selected
             'markov/nnrat-kernel-step-point-mass
             'markov/nnrat-kernel-step-point-mass-positive
             'markov/nnrat-kernel-iterate-one-point-mass
             'markov/nnrat-kernel-iterate-one-point-mass-positive
             'markov/nnrat-kernel-iterate-zero-point-mass-positive
             'markov/nnrat-point-mass-iterate-positive-along-trajectory}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
