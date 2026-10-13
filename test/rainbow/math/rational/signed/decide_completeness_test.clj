(ns rainbow.math.rational.signed.decide-completeness-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.decide-completeness :as completeness]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (completeness/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status (kernel/check env (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))))

(deftest exact-rational-decisions-are-universally-complete
  (let [env @checked-environment]
    (testing "the true result is complete from Bool through signed equivalence"
      (is (= #{'boolean/and-true-complete
               'nat/decide-at-most-true-complete
               'nnrat/decide-at-most-true-complete
               'signed/decide-at-most-true-complete
               'signed/decide-equivalent-true-complete
               'nat/decide-at-most-false-sound
               'nnrat/decide-at-most-false-sound
               'signed/decide-at-most-false-sound
               'signed/decide-equivalent-false-sound
               'nat/decide-at-most-false-complete
               'nnrat/decide-at-most-false-complete
               'signed/decide-at-most-false-complete
               'signed/decide-equivalent-false-complete}
             (set (keys (completeness/theorem-ids env)))))
      (doseq [[name id] (completeness/theorem-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
