(ns rainbow.proof-test
  (:require [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(deftest implication-transitivity-is-constructed-by-tactics
  (let [result (first-tactic-program/prove)]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= 9 (count (get-in result [:proof :proof/history]))))
    (is (false? (proof/contains-holes? (get-in result [:proof :proof/term]))))
    (is (= #{} (get-in result [:proof :proof/axioms])))))

(deftest proof-states-are-immutable-and-failure-is-nondestructive
  (let [started (proof/start (direct-term-corpus/build-environment) first-tactic-program/target)
        state (:state started)
        failed (tactic/run state (tactic/exact (term/bound 0)))
        progressed (tactic/run state (tactic/intro 'A))]
    (is (= :failure (:status failed)))
    (is (= state (:state failed)))
    (is (= :progress (:status progressed)))
    (is (= 1 (count (:proof/goals state))))
    (is (= "g-0" (get-in state [:proof/goals 0 :goal/id])))
    (is (= "g-1" (get-in progressed [:state :proof/goals 0 :goal/id])))))

(deftest intro-and-assumption-prove-polymorphic-identity
  (let [identity-type (:type (first direct-term-corpus/proofs))
        started (proof/start (direct-term-corpus/build-environment) identity-type {:universes ['u]})
        after-a (tactic/run (:state started) (tactic/intro 'A))
        after-x (tactic/run (:state after-a) (tactic/intro 'x))
        result (tactic/run (:state after-x) (tactic/assumption))]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= (:value (first direct-term-corpus/proofs))
           (get-in result [:proof :proof/term])))))
