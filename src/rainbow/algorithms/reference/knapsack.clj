(ns rainbow.algorithms.reference.knapsack
  "Executable 0/1 knapsack DP, matching the proved Rainbow cell rule.")

(defn cell [leave-value take-value] (if (<= leave-value take-value) take-value leave-value))

(defn knapsack
  "Max value of a 0/1 knapsack with integer capacity, items [weight value]."
  [capacity items]
  (let [dp (reduce
            (fn [row [w v]]
              (mapv (fn [c]
                      (if (>= c w)
                        (cell (row c) (+ v (row (- c w))))
                        (row c)))
                    (range (inc capacity))))
            (vec (repeat (inc capacity) 0))
            items)]
    (last dp)))
