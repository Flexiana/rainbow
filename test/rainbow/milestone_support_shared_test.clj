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

(deftest shared-add-compares-a-definition's-body
  ;; claim integrity A4: two definitions with
  ;; one type under one alias are two meanings, unlike two proofs of one statement
  (let [bool (function/const* 'data/Bool [])
        def-spec (fn [body] {:name 'test/pick :kind :definition :universes []
                             :type (function/arrow bool bool bool)
                             :value body})
        first-arg (function/lam [['a bool] ['b bool]] 'a)
        env (support/extend-with-shared @base-environment :shared-test [(def-spec first-arg)])]
    (testing "the same body, binder names changed: skipped"
      (let [again (support/extend-with-shared env :again [(def-spec (function/lam [['x bool] ['y bool]] 'x))])]
        (is (= (environment/resolve-id env 'test/pick) (environment/resolve-id again 'test/pick)))))
    (testing "a different body under the same alias and type: refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"one alias, two definitions"
           (support/extend-with-shared env :impostor [(def-spec (function/lam [['a bool] ['b bool]] 'b))]))))
    (testing "the same statement as a theorem where a definition is stored: refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"one alias, two definitions"
           (support/extend-with-shared env :impostor [(dissoc (def-spec first-arg) :kind)]))))))

(deftest a-spec-without-universes-has-none
  ;; add-spec passed a missing :universes through as nil, overriding add-declaration's []
  (let [bool (function/const* 'data/Bool [])
        spec {:name 'test/identity-bool :kind :definition
              :type (function/arrow bool bool) :value (function/lam [['b bool]] 'b)}
        without (support/add-spec @base-environment :test spec)
        with (support/add-spec @base-environment :test (assoc spec :universes []))]
    (is (= [] (:rainbow/universes (environment/declaration without (environment/resolve-id without 'test/identity-bool)))))
    (is (= (environment/resolve-id with 'test/identity-bool) (environment/resolve-id without 'test/identity-bool)))))
