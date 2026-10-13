(ns rainbow.math.finite.markov-full-support-irreducible-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-full-support-irreducible
             :as irreducible]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (irreducible/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest executable-full-support-certifies-index-hastings-irreducibility
  (let [env @checked-environment
        definitions (irreducible/definition-ids env)
        theorems (irreducible/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'mcmc/nnrat-hastings-index-irreducible-of-full-support
             'mcmc/nnrat-hastings-index-return-at-one-of-full-support
             'mcmc/nnrat-hastings-index-aperiodic-of-full-support}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (some? id) (str name))
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
