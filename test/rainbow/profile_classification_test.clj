(ns rainbow.profile-classification-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def base (delay (proposition/build-environment)))

(defn- activated [profile]
  (profile/activate @base profile))

(defn- add-theorem! [environment alias surface-type surface-value]
  (let [type (:term (elaborate/core-expression environment surface-type))
        value (:term (elaborate/core-expression environment surface-value))
        result (kernel/add-declaration
                environment
                {:rainbow/kind :theorem
                 :rainbow/aliases #{alias}
                 :rainbow/universes []
                 :rainbow/type type
                 :rainbow/value value
                 :rainbow/transparency :opaque
                 :rainbow/dependencies (into (term/constants type)
                                             (term/constants value))
                 :rainbow/provenance {:origin :native :producer :test}
                 :rainbow/schema-version 1})]
    (assert (= :accepted (:status result)) (pr-str result))
    [(:environment result) (get-in result [:declaration :rainbow/id])]))

(deftest an-axiom-free-target-classifies-as-constructive
  (let [[environment id]
        (add-theorem! @base 'test/trivially-true
                      (proposition/truth)
                      (proposition/const* 'proposition/trivial []))
        classification (profile/classify-declaration environment id)]
    (is (true? (:logical/constructive? classification)))
    (is (empty? (:logical/axiom-ids classification)))
    (is (= :constructive (:logical/profile classification)))
    (testing "a constructive target is admissible under every profile"
      (is (profile/within-profile? classification :constructive))
      (is (profile/within-profile? classification :classical))
      (is (profile/within-profile? classification :mathlib-logic)))))

(deftest a-target-is-classified-by-the-principle-it-actually-uses
  (let [activation (activated :propositional-extensional)
        environment (:environment activation)
        [environment id]
        (add-theorem!
         environment 'test/evidence-equals-truth
         (proposition/forall
          [['claim 'Prop :implicit] ['evidence 'claim]]
          (proposition/equality [:succ [:zero]] 'Prop 'claim
                                (proposition/truth)))
         (proposition/lam
          [['claim 'Prop :implicit] ['evidence 'claim]]
          (proposition/app
           (proposition/const* 'logic/proposition-extensionality [])
           'claim (proposition/truth)
           (proposition/introduce-equivalence
            'claim (proposition/truth)
            (proposition/lam [['ignored 'claim]]
                             (proposition/const* 'proposition/trivial []))
            (proposition/lam [['ignored (proposition/truth)]] 'evidence)))))
        classification (profile/classify-declaration environment id)]
    (is (= #{:propositional-extensionality} (set (:logical/principles classification))))
    (is (= (:logical/axiom-ids activation) (:logical/axiom-ids classification)))
    (is (= :propositional-extensional (:logical/profile classification)))
    (testing "it is admissible only under profiles that carry that principle"
      (is (profile/within-profile? classification :propositional-extensional))
      (is (profile/within-profile? classification :mathlib-logic))
      (is (not (profile/within-profile? classification :constructive)))
      (is (not (profile/within-profile? classification :classical))))))

(deftest choice-is-a-declared-principle-with-its-own-profile
  (let [activation (activated :choice-bearing)
        environment (:environment activation)
        axiom-id (first (:logical/axiom-ids activation))]
    (is (= #{:choice} (:logical/principles activation)))
    (is (= 1 (count (:logical/axiom-ids activation))))
    (is (= :choice (profile/principle-of environment axiom-id)))
    (is (= :none (:trusted-kernel-change activation)))
    (testing "the principle is an axiom, never a definition with a body"
      (is (= :axiom (:rainbow/kind
                     (rainbow.environment/declaration environment axiom-id))))
      (is (nil? (:rainbow/value
                 (rainbow.environment/declaration environment axiom-id)))))))

(deftest an-undeclared-axiom-blocks-every-profile-claim
  (let [type (:term (elaborate/core-expression @base (proposition/truth)))
        added (kernel/add-declaration
               @base
               {:rainbow/kind :axiom
                :rainbow/aliases #{'test/unvetted-assumption}
                :rainbow/universes []
                :rainbow/type type
                :rainbow/value nil
                :rainbow/transparency :opaque
                :rainbow/dependencies (term/constants type)
                :rainbow/provenance {:origin :native :producer :test}
                :rainbow/schema-version 1})
        environment (:environment added)
        [environment id]
        (add-theorem! environment 'test/rests-on-unvetted
                      (proposition/truth)
                      (proposition/const* 'test/unvetted-assumption []))
        classification (profile/classify-declaration environment id)]
    (is (= 1 (count (:logical/unknown-axiom-ids classification))))
    (is (empty? (:logical/principles classification)))
    (testing "an unrecognized axiom is never silently absorbed into a profile"
      (is (= :unknown (:logical/profile classification)))
      (is (not (profile/within-profile? classification :mathlib-complete-logic)))
      (is (not (profile/within-profile? classification :constructive))))))

(deftest a-cohort-is-summarized-for-routing
  (let [activation (activated :classical)
        environment (:environment activation)
        [environment constructive-id]
        (add-theorem! environment 'test/cohort-constructive
                      (proposition/truth)
                      (proposition/const* 'proposition/trivial []))
        [environment classical-id]
        (add-theorem! environment 'test/cohort-classical
                      (proposition/forall
                       [['claim 'Prop]]
                       (proposition/disjunction
                        'claim (proposition/negation 'claim)))
                      (proposition/const* 'logic/excluded-middle []))
        cohort (profile/classify-cohort environment
                                        [constructive-id classical-id]
                                        :constructive)]
    (is (= {:constructive 1 :classical 1} (:logical/by-profile cohort)))
    (is (empty? (:logical/unknown cohort)))
    (testing "the classical target is reported as outside a constructive request"
      (is (= #{classical-id} (:logical/outside cohort))))))
