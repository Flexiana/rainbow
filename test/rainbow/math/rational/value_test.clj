(ns rainbow.math.rational.value-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.value :as rvalue]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (rvalue/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest exact-rational-values-are-native-axiom-free
  (let [checked-environment @checked-environment
        theorems (rvalue/theorem-ids checked-environment)]
    (is (= #{'rvalue/half-times-one 'rvalue/half-times-half
             'rvalue/half-plus-half 'rvalue/quarter-plus-quarter
             'rvalue/one-times-quarter 'rvalue/one-over-half
             'rvalue/half-over-quarter 'rvalue/quarter-over-half}
           (set (keys theorems))))
    ;; Each exact rational worked value is proven axiom-free through the
    ;; cross-product equivalence relation (not pair equality).
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-values-match-exact-clojure-rationals
  ;; The same identities in exact Clojure rationals, as a correspondence check.
  (is (= 1/2 (* 1/2 1)))
  (is (= 1/4 (* 1/2 1/2)))
  (is (= 1 (+ 1/2 1/2)))
  (is (= 1/2 (+ 1/4 1/4)))
  (is (= 1/4 (* 1 1/4)))
  (is (= 2 (/ 1 1/2)))
  (is (= 2 (/ 1/2 1/4)))
  (is (= 1/2 (/ 1/4 1/2))))
