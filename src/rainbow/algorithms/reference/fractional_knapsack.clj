(ns rainbow.algorithms.reference.fractional-knapsack
  "Executable fractional knapsack greedy, matching the proved priority rule.")

(defn prefer? [density-a density-b] (<= density-b density-a))

(defn max-value
  "Maximum value of a fractional knapsack of capacity, items [value weight]."
  [capacity items]
  (loop [items (sort-by (fn [[v w]] (- (/ v w))) items), cap capacity, total 0]
    (if (or (empty? items) (zero? cap))
      total
      (let [[v w] (first items)]
        (if (<= w cap)
          (recur (rest items) (- cap w) (+ total v))
          (+ total (* v (/ cap w))))))))
