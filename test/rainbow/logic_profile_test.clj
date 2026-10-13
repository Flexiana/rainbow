(ns rainbow.logic-profile-test
  (:require [clojure.test :refer :all]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.prelude :as prelude]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.proof :as proof]
            [rainbow.search :as search]))

(def checked-environment (delay (proposition/build-environment)))

(deftest constructive-profile-adds-no-axioms
  (let [before @checked-environment
        activation (profile/activate before :constructive)]
    (is (= :activated (:status activation)))
    (is (empty? (:logical/axiom-ids activation)))
    (is (= before (:environment activation)))
    (is (= :none (:trusted-kernel-change activation)))))

(deftest mathlib-logic-profile-is-explicit-and-fully-auditable
  (let [activation (profile/activate @checked-environment :mathlib-logic)
        checked (:environment activation)
        declarations (:logical/declarations activation)
        ids (:logical/axiom-ids activation)]
    (is (= 3 (count declarations) (count ids)))
    (is (= #{:classical :propositional-extensionality :proof-irrelevance}
           (:logical/principles activation)))
    (doseq [declaration declarations]
      (is (= :axiom (:rainbow/kind declaration)))
      (is (nil? (:rainbow/value declaration)))
      (is (= #{(:rainbow/id declaration)}
             (kernel/axioms checked (:rainbow/id declaration))))
      (is (= :explicit-logical-profile
             (get-in declaration [:rainbow/provenance :producer]))))
    (is (= {:logical/profile :mathlib-logic
            :logical/principles
            (sorted-set :classical :proof-irrelevance
                        :propositional-extensionality)
            :logical/unknown-axiom-ids #{}
            :logical/within-profile? true}
           (profile/classify-axioms activation ids)))))

(deftest smaller-profile-does-not-silently-authorize-another-principle
  (let [classical (profile/activate @checked-environment :classical)
        extensional (profile/activate (:environment classical)
                                      :propositional-extensional)
        extensional-id (first (:logical/axiom-ids extensional))
        classification (profile/classify-axioms classical #{extensional-id})]
    (is (false? (:logical/within-profile? classification)))
    (is (= #{extensional-id} (:logical/unknown-axiom-ids classification)))
    (is (empty? (:logical/principles classification)))))

(deftest function-extensionality-is-explicit-and-proves-function-equality
  (let [activation (profile/activate @checked-environment
                                     :function-extensional)
        checked (:environment activation)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['claim 'Prop]]
           (proposition/equality
            [:imax [:succ [:zero]] [:succ [:zero]]]
            (proposition/arrow 'Prop 'Prop)
            (proposition/lam [['value 'Prop]] 'value)
            (proposition/lam [['value 'Prop]] 'value)))))
        result
        (search/prove
         (:state (proof/start checked target))
         {:states 16 :depth 16 :wall-ms 1000
          :native-logic-focus? true :native-logic-prune? true
          :native-reducible-focus? true
          :native-function-extensionality? true})]
    (is (= :activated (:status activation)))
    (is (= #{:function-extensionality}
           (:logical/principles activation)))
    (is (= :proved (:status result)) (pr-str result))
    (is (= :checked (get-in result [:kernel :status])))
    ;; Reflexivity can close this particular pointwise goal, but the outer
    ;; proof must visibly pass through the explicit extensionality axiom.
    (is (= (:logical/axiom-ids activation)
           (get-in result [:proof :proof/axioms])))))

(deftest function-extensionality-sees-through-a-reducible-set-carrier
  (let [base (prelude/extend-environment @checked-environment)
        activation (profile/activate base :mathlib-complete-logic)
        checked (prelude/extend-collections (:environment activation))
        zero [:zero]
        type-zero [:sort [:succ zero]]
        set-of (fn [element]
                 (proposition/app
                  (proposition/const* 'set/Set [zero]) element))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['A type-zero]
            ['left (set-of 'A)]
            ['right (set-of 'A)]
            ['pointwise
             (proposition/forall
              [['value 'A]]
              (proposition/equality
               [:succ zero] 'Prop
               (proposition/app 'left 'value)
               (proposition/app 'right 'value)))]]
           (proposition/equality [:succ zero] (set-of 'A) 'left 'right))))
        result
        (search/prove
         (:state (proof/start checked target))
         {:states 32 :depth 64 :wall-ms 5000
          :native-logic-focus? true :native-logic-prune? true
          :native-reducible-focus? true
          :native-proposition-extensionality? true
          :native-function-extensionality? true
          :native-structural-theorem-reuse? true})]
    (is (= :proved (:status result)) (pr-str result))
    (is (= :checked (get-in result [:kernel :status])))
    (is (some #(= :structural-theorem-reuse
                  (get-in % [:strategy :source]))
              (:attempts result)))
    (is (contains? (get-in result [:proof :proof/axioms])
                   (environment/resolve-id checked
                                           'logic/function-extensionality)))))

(deftest unknown-profile-rejects-with-available-options
  (let [data (try
               (profile/activate @checked-environment :silent-magic)
               (catch clojure.lang.ExceptionInfo exception
                 (ex-data exception)))]
    (is (= :logic-profile/unknown-profile (:error/category data)))
    (is (= (set (keys profile/profiles)) (:available data)))))

(deftest proposition-extensionality-is-typed-structural-reuse
  (let [activation (profile/activate @checked-environment
                                     :propositional-extensional)
        checked (:environment activation)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['left 'Prop :implicit] ['right 'Prop :implicit]
            ['equivalent (proposition/equivalence 'left 'right)]]
           (proposition/equality [:succ [:zero]] 'Prop 'left 'right))))
        baseline
        (search/prove (:state (proof/start checked target))
                      {:states 16 :depth 8 :wall-ms 1000
                       :native-logic-focus? true :native-logic-prune? true})
        structural
        (search/prove
         (:state (proof/start checked target))
         {:states 16 :depth 8 :wall-ms 1000
          :native-logic-focus? true :native-logic-prune? true
          :native-proposition-extensionality? true})]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status structural)))
    (is (= :checked (get-in structural [:kernel :status])))
    (is (= (:logical/axiom-ids activation)
           (get-in structural [:proof :proof/axioms])))
    (is (some #(= :structural-theorem-reuse
                  (get-in % [:strategy :source]))
              (:attempts structural)))))

(deftest structural-proof-plans-close-equality-and-equivalence-symmetry
  (let [activation (profile/activate @checked-environment
                                     :propositional-extensional)
        checked (:environment activation)
        targets
        (mapv
         (fn [surface]
           (:term (elaborate/core-expression checked surface)))
         [(proposition/forall
           [['left 'Prop] ['right 'Prop]]
           (proposition/equality
            [:succ [:zero]] 'Prop
            (proposition/equality [:succ [:zero]] 'Prop 'left 'right)
            (proposition/equality [:succ [:zero]] 'Prop 'right 'left)))
          (proposition/forall
           [['left 'Prop] ['right 'Prop]]
           (let [equivalence
                 (fn [left right]
                   (proposition/app
                    (proposition/const* 'proposition/equivalence [])
                    left right))]
             (proposition/equality
              [:succ [:zero]] 'Prop
              (equivalence 'left 'right)
              (equivalence 'right 'left))))])
        options
        {:states 32 :depth 16 :wall-ms 1000
         :native-logic-focus? true :native-logic-prune? true
         :native-proposition-extensionality? true
         :native-structural-theorem-reuse? true}
        results
        (mapv #(search/prove (:state (proof/start checked %)) options) targets)]
    (is (every? #(= :proved (:status %)) results))
    (is (every? #(= :checked (get-in % [:kernel :status])) results))
    (is (every? #(= (:logical/axiom-ids activation)
                    (get-in % [:proof :proof/axioms]))
                results))
    (is (every? #(some (fn [attempt]
                         (= :structural-proof-plan
                            (get-in attempt [:strategy :source])))
                       (:attempts %))
                results))))
