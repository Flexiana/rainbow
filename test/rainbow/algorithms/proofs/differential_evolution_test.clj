(ns rainbow.algorithms.proofs.differential-evolution-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.differential-evolution :as evolution]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.reference.differential-evolution :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          evolution/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest differential-mutation-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (evolution/definition-ids checked-environment)
        theorems (evolution/theorem-ids checked-environment)]
    (is (= #{'evolution/scaled-difference 'evolution/differential-mutation}
           (set (keys definitions))))
    (is (= #{'evolution/mutation-unfold
             'evolution/scaled-difference-example
             'evolution/mutation-example
             'evolution/unit-mutation-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-differential-evolution-mutates-vector-state-exactly
  ;; scaled-difference: 2 * ([1,2] - [0,0]) = [2,4].
  (is (= [2 4] (executable/scaled-difference 2 [1 2] [0 0])))
  ;; A real difference with nonzero c: 1 * ([3,4] - [1,1]) = [2,3].
  (is (= [2 3] (executable/scaled-difference 1 [3 4] [1 1])))
  ;; DE/rand/1 mutation: [0,0] + 1*([3,2]-[0,0]) = [3,2].
  (is (= [3 2] (executable/differential-mutation [0 0] 1 [3 2] [0 0])))
  ;; Unit mutation reduces to a plain sum of base and b: [1,1] + [2,3] = [3,4].
  (is (= [3 4] (executable/differential-mutation [1 1] 1 [2 3] [0 0])))
  ;; Scaled mutation with a nonzero difference: [1,1] + 1/2*([5,3]-[1,1]) = [3,2].
  (is (= [3 2] (executable/differential-mutation [1 1] 1/2 [5 3] [1 1])))
  ;; Binomial crossover picks per-component from mutant vs target.
  (is (= [1 20 3] (executable/binomial-crossover [1 2 3] [10 20 30]
                                                 [false true false])))
  ;; Greedy selection keeps the lower-objective vector.
  (is (= [0 0] (executable/select (fn [[a b]] (+ (* a a) (* b b)))
                                  [3 4] [0 0]))))
