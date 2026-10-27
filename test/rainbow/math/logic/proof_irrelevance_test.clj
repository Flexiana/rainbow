(ns rainbow.math.logic.proof-irrelevance-test
  (:require [clojure.test :refer :all]
            [rainbow.env-cache :as env-cache]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.proof-irrelevance :as pi]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]))

(def theorem 'logic/proof-irrelevance-from-proposition-extensionality)

(defn- declaration [env alias]
  (environment/declaration env (environment/resolve-id env alias)))

(def propext-environment
  (delay (:environment (profile/activate (proposition/build-environment)
                                         :propositional-extensional))))

(def installed (delay (pi/extend-environment @propext-environment)))

(deftest statement-is-the-proof-irrelevance-axiom
  ;; Declare the axiom AFTER installing, so the theorem cannot depend on it.
  (let [env (:environment (profile/activate @installed :proof-irrelevant))
        stated (:rainbow/type (declaration env theorem))
        axiom (:rainbow/type (declaration env 'logic/proof-irrelevance))]
    (is (= :axiom (:rainbow/kind (declaration env 'logic/proof-irrelevance))))
    (is (= :theorem (:rainbow/kind (declaration env theorem))))
    (is (= axiom stated) "syntactically equal kernel types")
    (is (true? (kernel/definitionally-equal? env axiom stated)))
    (is (= (:rainbow/universes (declaration env 'logic/proof-irrelevance))
           (:rainbow/universes (declaration env theorem))))))

(deftest only-axiom-is-proposition-extensionality
  (let [env @installed
        propext (environment/resolve-id env 'logic/proposition-extensionality)]
    (is (some? propext))
    (is (nil? (environment/resolve-id env 'logic/proof-irrelevance)))
    (is (nil? (environment/resolve-id env 'logic/excluded-middle)))
    (is (= #{propext} (kernel/axioms env theorem)))
    (is (= #{propext} (kernel/axioms env 'logic/prop-unit-equals-inhabited)))
    (doseq [alias ['logic/prop-unit-holds 'logic/prop-unit-eq-point
                   'logic/prop-unit-proofs-equal 'logic/prop-unit-transport-proofs-equal]]
      (is (= #{} (kernel/axioms env alias)) (str alias " is axiom-free")))))

(deftest prop-unit-is-a-one-constructor-proposition
  (let [env @installed]
    (is (= [:sort [:zero]] (:rainbow/type (declaration env 'logic/PropUnit))))
    (is (= :constructor (:rainbow/kind (declaration env 'logic/prop-unit))))
    (is (= 1 (get-in (declaration env 'logic/PropUnit.rec)
                     [:rainbow/recursor :constructor-count])))))

(deftest refuses-an-environment-without-proposition-extensionality
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"proposition-extensionality is not declared"
                        (pi/install (proposition/build-environment)))))

(deftest installs-on-the-default-checkpoint
  (let [base (env-cache/base)
        env (pi/extend-environment base)
        propext (environment/resolve-id env 'logic/proposition-extensionality)]
    (is (= #{propext} (kernel/axioms env theorem)))
    (is (= (:rainbow/type (declaration env 'logic/proof-irrelevance))
           (:rainbow/type (declaration env theorem))))
    (is (= env (pi/install env)) "re-installing is a no-op")))
