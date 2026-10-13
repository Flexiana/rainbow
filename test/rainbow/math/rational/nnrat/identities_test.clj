(ns rainbow.math.rational.nnrat.identities-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.division :as division]))

(defn- ensure-extension [checked-environment alias extend]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (extend checked-environment)))

(def checked-environment
  (delay
      (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/strict-contraction-stabilization/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Stabilization checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          (ensure-extension 'nnrat/divide division/extend-environment)
          identities/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nnrat-identities-are-axiom-free-and-checked
  (let [checked-environment @checked-environment
        ids (identities/theorem-ids checked-environment)]
    (is (= #{'nnrat/add-zero-right 'nnrat/add-zero-left
             'nnrat/multiply-one-right 'nnrat/multiply-one-left
             'nnrat/multiply-zero-right 'nnrat/multiply-zero-left
             'nnrat/reciprocal-one 'nnrat/divide-one-right}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-nnrat-identity-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id (environment/resolve-id checked-environment
                                           'nnrat/divide-one-right)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result (kernel/check checked-environment [:const zero-id []]
                             (:rainbow/type theorem)
                             (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
