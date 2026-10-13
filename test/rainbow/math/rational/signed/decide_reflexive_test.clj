(ns rainbow.math.rational.signed.decide-reflexive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.decide-reflexive :as reflexive]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (reflexive/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status (kernel/check env (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))))

(deftest exact-order-decisions-choose-the-true-branch-on-every-tie
  (let [env @checked-environment]
    (is (= #{'nat/decide-at-most-reflexive-true
             'nnrat/decide-at-most-reflexive-true
             'signed/decide-at-most-reflexive-true}
           (set (keys (reflexive/theorem-ids env)))))
    (doseq [[name id] (reflexive/theorem-ids env)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
