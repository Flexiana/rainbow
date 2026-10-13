(ns rainbow.milestone-support-shared-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def base-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (:environment checkpoint))))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(deftest shared-add-skips-verbatim-duplicates-and-rejects-divergence
  (testing "the verbatim-duplicate case: installing the same spec twice
            through the shared path leaves one declaration and does not
            throw -- the case that otherwise demands marker-guarded entry"
    (let [env (support/extend-with-shared
               @base-environment :shared-test [identities/add-zero-right-spec])
          id-once (environment/resolve-id env 'nnrat/add-zero-right)
          env-again (support/extend-with-shared
                     env :shared-test-again [identities/add-zero-right-spec])
          id-twice (environment/resolve-id env-again 'nnrat/add-zero-right)]
      (is (some? id-once))
      (is (= id-once id-twice))))
  (testing "the divergence case: a DIFFERENT statement under an existing
            alias is refused loudly, never skipped -- skipping here would
            be the D20-shape silent corruption"
    (let [env (support/extend-with-shared
               @base-environment :shared-test [identities/add-zero-right-spec])
          impostor {:name 'nnrat/add-zero-right :universes []
                    ;; a well-formed but WRONG statement under the alias
                    :type (function/forall
                           [['value nnrat]]
                           (function/app
                            (function/const* 'nnrat/equivalent [])
                            'value 'value))
                    :value (function/lam
                            [['value nnrat]]
                            (function/app
                             (function/const* 'nnrat/equivalent-reflexive [])
                             'value))}]
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"one alias, two statements"
           (support/extend-with-shared env :impostor [impostor]))))))
