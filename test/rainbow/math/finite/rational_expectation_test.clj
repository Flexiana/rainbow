(ns rainbow.math.finite.rational-expectation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-expectation :as expectation]
            [rainbow.math.nat.semiring :as nat-semiring]
            [rainbow.math.nonnegative-rational :as nnrat]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/or-contraction/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "OR contraction checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-semiring/extend-environment
          nnrat/extend-environment
          expectation/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-rational-expectation-is-generic-native-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (expectation/definition-ids checked-environment)
        theorems (expectation/theorem-ids checked-environment)]
    (is (= #{'list/nnrat-map-sum 'probability/nnrat-expectation}
           (set (keys definitions))))
    (is (= #{'list/nnrat-map-sum-respects-equivalence
             'nnrat/finite-expectation-respects-equivalence}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
