(ns rainbow.math.nonnegative-rational-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
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
          nnrat/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Test expression failed elaboration" {:result result})))
    (:term result)))

(defn- normalized [checked-environment expression]
  (let [result (kernel/normalize checked-environment
                                 (core checked-environment expression))]
    (when-not (= :normalized (:status result))
      (throw (ex-info "Test expression failed normalization"
                      {:result result})))
    (:term result)))

(deftest nonnegative-rational-foundation-is-native-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (nnrat/definition-ids checked-environment)
        theorems (nnrat/theorem-ids checked-environment)]
    (is (= #{'nnrat/NonnegativeRational 'nnrat/make 'nnrat/numerator
             'nnrat/denominator-predecessor 'nnrat/denominator
             'nnrat/combine-denominator-predecessors
             'nnrat/zero 'nnrat/one 'nnrat/half 'nnrat/quarter
             'nnrat/equivalent 'nnrat/add 'nnrat/multiply}
           (set (keys definitions))))
    (is (= #{'nnrat/denominator-combine
             'nnrat/add-respects-equivalence
             'nnrat/equivalent-reflexive
             'nnrat/equivalent-symmetric
             'nnrat/equivalent-transitive
             'nnrat/multiply-respects-equivalence}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest evaluator-computes-half-times-half-as-quarter
  (let [checked-environment @checked-environment
        product
        [:app [:const 'nnrat/multiply []]
         [:const 'nnrat/half []]
         [:const 'nnrat/half []]]]
    (is (= (normalized checked-environment product)
           (normalized checked-environment [:const 'nnrat/quarter []])))))
