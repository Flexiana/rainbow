(ns rainbow.math.finite.markov-positive-step-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-positive-step :as positive-step]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (positive-step/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest positive-support-propagates-through-a-listed-edge
  (let [env @checked-environment
        definitions (positive-step/definition-ids env)
        theorems (positive-step/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-step-positive-of-member
             'markov/nnrat-kernel-iterate-positive-successor-of-member
             'markov/nnrat-kernel-iterate-positive-along-trajectory}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
