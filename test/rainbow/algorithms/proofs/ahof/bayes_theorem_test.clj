(ns rainbow.algorithms.proofs.ahof.bayes-theorem-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.bayes-theorem :as bayes]
            [rainbow.algorithms.reference.bayes-theorem :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          bayes/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bayes-theorem-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (bayes/definition-ids checked-environment)
        theorems (bayes/theorem-ids checked-environment)]
    (is (= #{'bayes/posterior} (set (keys definitions))))
    (is (= #{'bayes/posterior-example 'bayes/uninformative-evidence}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-bayes-theorem
  (is (= 1 (executable/posterior 3/4 1/2 3/8)))
  (is (= 3/4 (executable/posterior 1/2 3/4 1/2)))
  ;; disease prevalence 1/100, test sens 9/10, false-pos 1/10
  ;; posterior = .009 / (.009 + .099) = 9/108 = 1/12
  (is (= 1/12 (executable/posterior-from-marginals 9/10 1/100 1/10))))
