(ns rainbow.level-equivalence-test
  "Levels are compared by value: two levels are equal when they agree under every assignment of
  naturals to their parameters (term/level-equivalent?). Before 1.4.4 the kernel compared normal
  forms, which missed max (succ u) u = succ u and the regroupings of a three-way max."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(def u [:param 'u]) (def v [:param 'v]) (def w [:param 'w])
(defn- succ [l] [:succ l]) (defn- mx [a b] [:max a b]) (defn- imx [a b] [:imax a b])

(defn- value [level env]
  (case (first level)
    :zero 0
    :param (env (second level))
    :succ (inc (value (second level) env))
    :max (max (value (second level) env) (value (nth level 2) env))
    :imax (let [b (value (nth level 2) env)] (if (zero? b) 0 (max (value (second level) env) b)))))

(def grid (for [a (range 5) b (range 5) c (range 5)] {'u a 'v b 'w c}))
(defn- equal-on-grid? [a b] (every? #(= (value a %) (value b %)) grid))

(defn- random-level [^java.util.Random r depth]
  (if (or (zero? depth) (< (.nextDouble r) 0.25))
    (case (.nextInt r 4) 0 [:zero] 1 u 2 v 3 w)
    (case (.nextInt r 4)
      0 (succ (random-level r (dec depth)))
      1 (mx (random-level r (dec depth)) (random-level r (dec depth)))
      2 (imx (random-level r (dec depth)) (random-level r (dec depth)))
      3 (random-level r (dec depth)))))

(deftest equal-levels-the-normal-form-missed
  (doseq [[a b] [[(mx (succ u) u) (succ u)]
                 [(mx u (mx v w)) (mx (mx u v) w)]
                 [(imx u (succ v)) (mx u (succ v))]
                 [(imx u u) u]
                 [(imx u (mx v (succ w))) (mx u (mx v (succ w)))]
                 [(imx (mx u v) w) (mx (imx u w) (imx v w))]]]
    (is (term/level-equivalent? a b) (pr-str a b))
    (is (term/level-equivalent? b a) (pr-str b a))))

(deftest different-levels-stay-different
  (doseq [[a b] [[(mx u (imx v u)) (mx u v)]   ; u = 0, v = 1: 0 against 1
                 [(imx u v) (mx u v)]           ; v = 0, u = 1
                 [(mx (imx u v) v) (mx u v)]    ; v = 0, u = 1: 0 against 1
                 [(succ u) u]
                 [(mx u v) u]
                 [[:zero] (imx u v)]]]
    (is (not (term/level-equivalent? a b)) (pr-str a b))))

(deftest equivalence-agrees-with-evaluation
  ;; sound: equivalent levels agree on every point of the grid; complete on these sizes: levels that
  ;; agree on the grid (offsets at most 3, parameters 0..4) are found equivalent
  (let [r (java.util.Random. 20261026)
        pairs (repeatedly 4000 #(vector (random-level r 4) (random-level r 4)))
        equal (filter #(apply equal-on-grid? %) pairs)]
    (is (< 50 (count equal)) "the sample has equal pairs that are not identical")
    (doseq [[a b] pairs]
      (is (= (equal-on-grid? a b) (term/level-equivalent? a b)) (pr-str a b)))))

(deftest the-kernel-compares-sorts-by-value
  (let [env (environment/empty-environment)
        sort-of (fn [l] [:sort l])]
    (is (true? (kernel/definitionally-equal? env (sort-of (mx (succ u) u)) (sort-of (succ u)))))
    (is (false? (kernel/definitionally-equal? env (sort-of (mx u v)) (sort-of u))))
    (testing "a function whose domain is written with an equal level checks against the Pi type"
      (is (= :checked (:status (kernel/check env
                                             [:lam (sort-of (mx (succ u) u)) [:bound 0] :explicit]
                                             [:pi (sort-of (succ u)) (sort-of (succ u)) :explicit]
                                             #{'u})))))
    (testing "an unequal level is still refused"
      (is (= :rejected (:status (kernel/check env
                                              [:lam (sort-of (mx u v)) [:bound 0] :explicit]
                                              [:pi (sort-of u) (sort-of u) :explicit]
                                              #{'u 'v})))))))
