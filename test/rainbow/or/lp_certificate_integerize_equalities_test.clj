(ns rainbow.or.lp-certificate-integerize-equalities-test
  "Regression: integerize must scale :equalities and :equality-prices too.

  Bug (found in an audit, 2026-09-10): integerize scaled :matrix/:capacities/:margins/
  :plan/:prices but left :equalities and :equality-prices at their original
  magnitude. Since expand-equalities turns each {:row a :value v} with free price p
  into matrix rows +-a, capacities +-v and prices max(p,0)/max(-p,0), the scaled
  kernel check then ran on an instance whose equality part was inconsistent with
  its (scaled) inequality part -- e.g. a scaled plan could spuriously satisfy an
  unscaled equality that the original plan does not satisfy.

  These are pure-data assertions on integerize (no kernel/checkpoint), so they run
  fast and cannot silently regress: :row scales by d (like :matrix), :value by d*d
  (like :capacities), :equality-prices by d (like :prices), and the equality's
  feasibility relationship is preserved under scaling."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private candidate
  {:matrix [[1]] :capacities [1] :margins [1] :plan [1/2] :prices [2]
   :equalities [{:row [1] :value 1}] :equality-prices [-2]})

(defn- lhs [row plan] (reduce + 0 (map * row plan)))

(deftest integerize-scales-equalities-consistently
  (testing "equalities and equality-prices scale with the rest (d, d*d, d)"
    (let [[scaled d] (lp/integerize candidate)
          dd (* d d)]
      (is (= 2 d) "fractional plan 1/2 forces scale 2")
      (is (= [{:row [2] :value 4}] (:equalities scaled))
          ":row scales by d and :value by d*d")
      (is (= [-4] (:equality-prices scaled))
          ":equality-prices scale by d")
      ;; the scaled equalities are consistent with the scaled inequality data
      (is (= [4] (:capacities scaled)))
      (is (= [1] (:plan scaled))))))

(deftest integerize-preserves-equality-feasibility
  (testing "scaling does not change whether the plan satisfies the equality --
            the bug let a scaled plan spuriously satisfy an unscaled equality"
    (let [[scaled d] (lp/integerize candidate)
          {orig-row :row orig-val :value} (first (:equalities candidate))
          {scl-row :row scl-val :value} (first (:equalities scaled))
          orig-ok (= (lhs orig-row (:plan candidate)) orig-val)
          scl-ok (= (lhs scl-row (:plan scaled)) scl-val)]
      (is (= orig-ok scl-ok)
          "scaled-plan equality feasibility must match original-plan equality feasibility")
      (is (false? scl-ok)
          "for this candidate the plan does NOT satisfy the equality (1*1/2 != 1);
           pre-fix the scaled plan spuriously satisfied the unscaled equality (1*1 = 1)"))))

(deftest integer-scale-covers-equality-denominators
  (testing "an equality whose denominator appears NOWHERE else still forces D, and
            the scaled instance is fully integral (integer-scale must scan
            :equalities and :equality-prices, not just the inequality data)"
    (let [inst {:matrix [[1]] :capacities [1] :margins [1] :plan [1] :prices [1]
                :equalities [{:row [1/3] :value 2/3}] :equality-prices [1/3]}
          [scaled d] (lp/integerize inst)]
      (is (= 3 d) "D must clear the equality's 1/3 denominators")
      (is (= [{:row [1] :value 6}] (:equalities scaled))
          ":row 1/3*3=1 ; :value 2/3*9=6")
      (is (= [1] (:equality-prices scaled)) ":equality-prices 1/3*3=1")
      (is (every? #(not (ratio? (rationalize %)))
                  (concat (apply concat (:matrix scaled)) (:capacities scaled)
                          (:margins scaled) (:plan scaled) (:prices scaled)
                          (mapcat :row (:equalities scaled))
                          (map :value (:equalities scaled))
                          (:equality-prices scaled)))
          "no denominator survives scaling anywhere, equalities included"))))

(deftest integerize-noop-on-integral-equalities
  (testing "already-integral instance with equalities is returned unchanged (scale 1)"
    (let [inst {:matrix [[1]] :capacities [2] :margins [1] :plan [2] :prices [1]
                :equalities [{:row [1] :value 2}] :equality-prices [3]}
          [scaled d] (lp/integerize inst)]
      (is (= 1 d))
      (is (identical? inst scaled) "integral data returns the very same value"))))
