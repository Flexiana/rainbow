(ns rainbow.rewrite-test
  (:require [clojure.test :refer :all]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.math.logic.equality :as equality]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]))

(defn theorem-target [environment alias]
  (:rainbow/type (environment/declaration environment
                                          (environment/resolve-id environment alias))))

(defn introduce [environment target count]
  (tactic/run (:state (proof/start environment target {:universes ['u]}))
              (tactic/repeat (tactic/intro) {:max count})))

(deftest forward-rewrite-proves-substitution
  (let [environment (equality/build-environment)
        introduced (introduce environment
                              (theorem-target environment 'equality/substitution) 6)
        rewritten (tactic/run (:state introduced) (tactic/rewrite [:bound 2]))
        result (tactic/run (:state rewritten) (tactic/assumption))]
    (is (= :progress (:status rewritten)))
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= :rewrite (get-in result [:proof :proof/history 6 :event/tactic])))))

(deftest backward-rewrite-proves-reverse-substitution
  (let [environment (equality/build-environment)
        introduced (introduce environment
                              (theorem-target environment 'equality/reverse-substitution) 6)
        rewritten (tactic/run (:state introduced)
                              (tactic/rewrite [:bound 2] {:direction :backward}))
        result (tactic/run (:state rewritten) (tactic/assumption))]
    (is (= :progress (:status rewritten)))
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))))

(deftest missing-rewrite-occurrence-fails-without-changing-state
  (let [environment (equality/build-environment)
        introduced (introduce environment
                              (theorem-target environment 'equality/substitution) 6)
        state (:state introduced)
        ;; h proves x = y, while this target is changed to P A's type and contains neither.
        unrelated (assoc-in state [:proof/goals 0 :goal/target] '[:sort [:zero]])
        result (tactic/run unrelated (tactic/rewrite [:bound 2]))]
    (is (= :failure (:status result)))
    (is (= :tactic/no-rewrite-occurrence
           (get-in result [:failure :failure/category])))
    (is (= unrelated (:state result)))))

(deftest simplification-closes-reflexivity-and-bounds-rewrite-cycles
  (let [environment (equality/build-environment)
        reflexive-surface (equality/forall
                           [['A equality/sort-u] ['x 'A]]
                           (equality/eq 'A 'x 'x))
        reflexive-target (:term (elaborate/core-expression environment reflexive-surface))
        reflexive-intros (introduce environment reflexive-target 2)
        reflexive-result (tactic/run (:state reflexive-intros) (tactic/simplify []))
        cycle-surface (equality/forall
                       [['A equality/sort-u] ['x 'A] ['y 'A]
                        ['h (equality/eq 'A 'x 'y)]
                        ['hs (equality/eq 'A 'y 'x)]
                        ['P (equality/arrow 'A 'Prop)]]
                       (equality/app 'P 'y))
        cycle-target (:term (elaborate/core-expression environment cycle-surface))
        cycle-intros (introduce environment cycle-target 6)
        cycled (tactic/run (:state cycle-intros)
                           (tactic/simplify [[:bound 2] [:bound 1]] {:max 4}))]
    (is (= :proved (:status reflexive-result)))
    (is (= :checked (get-in reflexive-result [:kernel :status])))
    (is (= :progress (:status cycled)))
    (is (= 4 (:steps cycled)))
    (is (= :repeat/max-reached (:reason cycled)))))

(deftest calc-chains-checked-equality-evidence
  (let [environment (equality/build-environment)
        target (theorem-target environment 'equality/transitive)
        introduced (introduce environment target 6)
        result (tactic/run (:state introduced)
                           (tactic/calc [[:bound 1] [:bound 0]]))]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= :calc (get-in result [:proof :proof/history 6 :event/tactic])))))
