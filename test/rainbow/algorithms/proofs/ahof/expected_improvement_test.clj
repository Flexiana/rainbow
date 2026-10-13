(ns rainbow.algorithms.proofs.ahof.expected-improvement-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.expected-improvement :as ei]
            [rainbow.algorithms.reference.expected-improvement :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          ei/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest expected-improvement-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (ei/definition-ids checked-environment)
        theorems (ei/theorem-ids checked-environment)]
    (is (= #{'expected-improvement/ei} (set (keys definitions))))
    (is (= #{'expected-improvement/ei-unfold
             'expected-improvement/ei-example
             'expected-improvement/ei-at-least-exploitation
             'expected-improvement/ei-at-least-exploitation-universal}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-expected-improvement-selects
  (is (= 10 (executable/ei 3 2 1 4)))
  ;; Candidate b has less improvement but far more exploration value.
  (let [stats {:a [4 1 1 1] :b [1 1 3 3]}]
    (is (= :b (executable/select stats [:a :b])))))
