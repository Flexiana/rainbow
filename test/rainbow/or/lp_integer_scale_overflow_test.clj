(ns rainbow.or.lp-integer-scale-overflow-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.canonical :as canonical]))

;; Adjacent denominators are coprime and their LCM exceeds Long/MAX_VALUE.
(def wide {:matrix [[(/ 1 4000000000) (/ 1 4000000001)]]
           :capacities [1] :margins [0 0] :plan [0 0] :prices [0]})

(deftest scale-exceeds-long-without-losing-exactness
  (is (= 16000000004000000000N (lp/integer-scale wide)))
  (let [[scaled d] (lp/integerize wide)]
    (is (= 16000000004000000000N d))
    (is (= [[4000000001N 4000000000N]] (:matrix scaled)))
    (is (= [(*' d d)] (:capacities scaled)))
    (is (= 1 (lp/integer-scale scaled)))))

(deftest small-and-integral-identities-remain-stable
  (is (= Long (class (lp/integer-scale {:matrix [[1/2 1/3]]}))))
  (is (= 6 (lp/integer-scale {:matrix [[1/2 1/3]]})))
  (let [integral {:matrix [[1]] :capacities [4] :margins [2] :plan [4] :prices [2]}
        [scaled d] (lp/integerize integral)]
    (is (= Long (class d)))
    (is (= 1 d))
    (is (identical? integral scaled))
    (is (= (canonical/content-id integral) (canonical/content-id scaled)))))

(deftest wide-scale-preserves-a-nonzero-equality-witness
  (let [row (first (:matrix wide))
        instance (assoc wide :plan [4000000000 0]
                             :equalities [{:row row :value 1}]
                             :equality-prices [-1])
        [scaled d] (lp/integerize instance)
        dot (fn [a b] (reduce +' 0 (map *' a b)))
        equality (first (:equalities scaled))]
    (is (= 1 (dot row (:plan instance))))
    (is (= (:value equality) (dot (:row equality) (:plan scaled))))
    (is (= [(- d)] (:equality-prices scaled)))
    (is (= 1 (lp/integer-scale scaled)))))
