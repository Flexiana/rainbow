(ns rainbow.algorithms.proofs.fibonacci-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.fibonacci :as fibonacci]
            [rainbow.algorithms.reference.fibonacci :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          fibonacci/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fibonacci-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (fibonacci/definition-ids checked-environment)
        theorems (fibonacci/theorem-ids checked-environment)]
    (is (= #{'fibonacci/pair 'fibonacci/fib} (set (keys definitions))))
    (is (= #{'fibonacci/pair-step-unfold 'fibonacci/fib-zero
             'fibonacci/fib-one 'fibonacci/fib-seven}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-fibonacci-matches
  (is (= 0 (executable/fib 0)))
  (is (= 1 (executable/fib 1)))
  (is (= 13 (executable/fib 7)))
  (is (= [0 1 1 2 3 5 8 13] (mapv executable/fib (range 8))))
  ;; Fibonacci-search probes are symmetric within the interval.
  (let [[p1 p2] (executable/fib-search-probes 0 1 5)]
    (is (= 1 (+ p1 p2)))))
