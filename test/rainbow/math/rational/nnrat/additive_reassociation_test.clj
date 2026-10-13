(ns rainbow.math.rational.nnrat.additive-reassociation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.additive-reassociation :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/vector-equivalence-laws/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Vector-equivalence checkpoint rejected"
                        {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest additive-reassociation-laws-are-native-general-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (laws/theorem-ids checked-environment)]
    (is (= #{'nnrat/add-associative
             'nnrat/add-swap-right
             'nnrat/add-four-reorder}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest malformed-additive-reassociation-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id checked-environment 'nnrat/add-four-reorder)
        theorem (environment/declaration checked-environment theorem-id)
        trivial-id
        (environment/resolve-id checked-environment 'proposition/trivial)
        result (kernel/check checked-environment [:const trivial-id []]
                             (:rainbow/type theorem)
                             (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
