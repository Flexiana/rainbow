(ns rainbow.or-value-iteration-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.algorithms.reference.value-iteration :as value-iteration]))

(def worked-model
  {:states [0 1]
   :actions [0]
   :transition (fn [_state action next-state]
                 (if (= action next-state) 1 0))
   :reward (fn [_state _action] 0)
   :discount 0
   :fallback (constantly 0)})

(def controlled-model
  {:states [0 1]
   :actions [0 1]
   :transition (fn [_state action next-state]
                 (if (= action next-state) 1 0))
   :reward (fn [state action] (+ state action))
   :discount 1/2
   :fallback (constantly 0)})

(deftest exact-reference-value-iteration-matches-the-worked-proof-instance
  (is (= {0 0, 1 0}
         (value-iteration/value-iterate worked-model 0 {0 0, 1 0})))
  (is (= {0 0, 1 0}
         (value-iteration/value-iterate worked-model 1 {0 0, 1 0})))
  (is (= {0 0N, 1 0N}
         (value-iteration/value-iterate worked-model 2 {0 0, 1 0})))
  (is (= [0 0]
         (mapv #(value-iteration/greedy-action
                 worked-model {0 0, 1 0} %)
               [0 1]))))

(deftest exact-reference-handles-nonzero-discount-and-action-choice
  (is (= {0 1, 1 2}
         (value-iteration/value-iterate controlled-model 1 {0 0, 1 0})))
  (is (= {0 2N, 1 3N}
         (value-iteration/value-iterate controlled-model 2 {0 0, 1 0})))
  (is (= [1 1]
         (mapv #(value-iteration/greedy-action
                 controlled-model {0 1, 1 2} %)
               [0 1]))))

(deftest executable-model-refuses-invalid-evidence
  (testing "transition rows must be normalized"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not normalized"
         (value-iteration/value-iterate
          (assoc worked-model :transition (fn [_ _ _] 0))
          1 {0 0, 1 0}))))
  (testing "fallback actions must be admissible"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"outside the action space"
         (value-iteration/value-iterate
          (assoc worked-model :fallback (constantly 2))
          1 {0 0, 1 0}))))
  (testing "initial values must cover the finite state space"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"Initial values must cover"
         (value-iteration/value-iterate worked-model 1 {0 0})))))
