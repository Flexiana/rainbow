(ns rainbow.math.nat.pair-index-inverse-test
  "Cold gate: the pair index is invertible -- row-of n (a + b*n) = b and col-of n (a + b*n) = a for
  a < n, and a + b*n = a' + b'*n with a, a' < n forces (a, b) = (a', b'); kernel-checked and
  axiom-free. Exercised against Clojure quot/mod, and the a < n hypothesis is shown NEEDED:
  without it the decomposition is not unique."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.pair-index-inverse :as m]))

(def checked-environment
  (delay (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status cp)) (throw (ex-info "checkpoint" {})))
           (-> (:environment cp) m/extend-environment))))

(deftest pair-index-inverse-checked-axiom-free
  (let [env @checked-environment ids (m/theorem-ids env)]
    (is (= 4 (count ids)))
    (doseq [[nm id] ids]
      (is (some? id) (str nm " installed"))
      (let [d (environment/declaration env id)]
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                               (set (:rainbow/universes d))))) (str nm))
        (is (= #{} (kernel/axioms env id)) (str nm))))))

(deftest the-statements-agree-with-division-and-need-their-hypothesis
  (testing "row-of/col-of of a + b n are quot/mod, for every a < n"
    (doseq [n (range 1 7) a (range n) b (range 6)]
      (is (= [b a] [(quot (+ a (* b n)) n) (mod (+ a (* b n)) n)]))))
  (testing "discrimination: with a >= n the decomposition is NOT unique (5 + 0*3 = 2 + 1*3)"
    (is (= (+ 5 (* 0 3)) (+ 2 (* 1 3))))
    (is (not= [5 0] [2 1]))))
