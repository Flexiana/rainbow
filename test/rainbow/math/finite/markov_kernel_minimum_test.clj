(ns rainbow.math.finite.markov-kernel-minimum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-kernel-minimum :as minimum]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (minimum/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nested-finite-argmins-select-a-kernel-entry-inside-the-carrier
  (let [env @checked-environment
        definitions (minimum/definition-ids env)
        theorems (minimum/theorem-ids env)]
    (is (= #{'markov/nnrat-kernel-row-argmin
             'markov/nnrat-kernel-argmin-source
             'markov/nnrat-kernel-minimum}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-row-argmin-member
             'markov/nnrat-kernel-argmin-source-member
             'markov/nnrat-kernel-minimum-positive
             'markov/nnrat-kernel-minimum-bounds-entry
             'markov/nnrat-kernel-minimum-positive-lower-bound}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
