(ns rainbow.math.finite.rational-argmax-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-argmax :as argmax]
            [rainbow.math.logic.maximum-expected-utility :as meu]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/decision-guarantee-audit-v0/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF audit checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          argmax/extend-environment
          meu/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-rational-argmax-foundations-are-native-and-axiom-free
  (let [checked-environment @checked-environment]
    (is (= #{'decision/nnrat-select
             'list/nnrat-argmax-from
             'decision/finite-nnrat-argmax}
           (set (keys (argmax/definition-ids checked-environment)))))
    (doseq [[name id] (argmax/theorem-ids checked-environment)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest ahof-d17-is-computed-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (meu/theorem-ids checked-environment)
        selected-id (environment/resolve-id checked-environment
                                            'ahof-d17/selected-action)
        renegotiate-id (environment/resolve-id checked-environment
                                               'ahof-d17/renegotiate)
        selected (kernel/normalize checked-environment [:const selected-id []])
        renegotiate (kernel/normalize checked-environment
                                      [:const renegotiate-id []])]
    (is (= #{'ahof-d17/accept-is-action
             'ahof-d17/probabilities-normalized
             'ahof-d17/expected-utility-is-finite-expectation
             'ahof-d17/selected-is-renegotiate
             'ahof-d17/selected-is-member
             'ahof-d17/selected-dominates
             'ahof-d17/maximum-expected-utility}
           (set (keys theorems))))
    (is (= :normalized (:status selected)))
    (is (= (:term renegotiate) (:term selected)))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
