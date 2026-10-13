(ns rainbow.algorithms.reference.finite-markov-reference-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.algorithms.reference.finite-markov-reference :as reference]))

(deftest sparse-exact-column-reference-replays-certificate
  (let [kernel [[1 0] [1/2 1/2]]
        stationary [1 0]
        initial [0 1]]
    (testing "the executable reference preserves the certificate's exact model"
      (is (reference/normalized-kernel? kernel))
      (is (reference/stationary? kernel stationary))
      (is (= [1/2 1/2] (reference/step kernel initial)))
      (is (reference/mass-preserving? kernel initial))
      (is (= 1/2 (reference/total-variation
                  (reference/step kernel initial)
                  (reference/step kernel stationary))))
      (is (every? #(reference/envelope? kernel 1/2 % initial stationary)
                  (range 0 11))))))

(deftest malformed-kernels-are-rejected
  (testing "shape and normalization are checked before execution"
    (is (false? (reference/square-kernel? [[1 0] [1]])))
    (is (false? (reference/normalized-kernel? [[1 0] [1/2 1/4]])))
    (is (thrown? AssertionError
                 (reference/step [[1 0] [1/2 1/4]] [0 1])))))

(deftest mass-preservation-rejects-invalid-kernels
  (is (false? (reference/mass-preserving? [[1 0] [1/2 1/4]] [0 1])))
  (is (reference/mass-preserving? [[1 0] [1 0]] [1/3 2/3])))

(deftest envelope-rejects-out-of-range-factors
  (is (false? (reference/unit-factor? -1/4)))
  (is (false? (reference/unit-factor? 5/4)))
  (is (false? (reference/envelope? [[1 0] [1/2 1/2]] -1/4 1 [0 1] [1 0]))))

(deftest iterates-compose
  (let [kernel [[1 0] [1/2 1/2]]
        mass [1/4 3/4]]
    (is (every? (fn [[n m]]
                  (= (reference/iterate kernel (+ n m) mass)
                     (reference/iterate kernel n
                                         (reference/iterate kernel m mass))))
                (for [n (range 4) m (range 4)] [n m])))))

(deftest signed-masses-are-rejected
  (is (false? (reference/nonnegative-mass? [1/2 -1/2])))
  (is (thrown? AssertionError
               (reference/step [[1 0] [1/2 1/2]] [1 -1]))))

(deftest total-variation-is-symmetric-and-dimension-safe
  (is (= 1/4 (reference/total-variation [1/2 1/2] [1/4 3/4])))
  (is (= (reference/total-variation [1/2 1/2] [1/4 3/4])
         (reference/total-variation [1/4 3/4] [1/2 1/2])))
  (is (= 0 (reference/total-variation [1/3 2/3] [1/3 2/3])))
  (is (thrown? AssertionError
               (reference/total-variation [1] [1 0]))))
