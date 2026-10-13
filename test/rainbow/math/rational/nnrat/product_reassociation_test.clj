(ns rainbow.math.rational.nnrat.product-reassociation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o32-coordinate-search/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O32 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          commutative/extend-environment
          reassociation/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest product-reassociation-is-native-general-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (reassociation/theorem-ids checked-environment)]
    (is (= #{'nnrat/multiply-associative
             'nnrat/multiply-swap-right
             'nnrat/multiply-four-reorder}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest malformed-reassociation-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id (environment/resolve-id checked-environment
                                           'nnrat/multiply-four-reorder)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result (kernel/check checked-environment [:const zero-id []]
                             (:rainbow/type theorem)
                             (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
