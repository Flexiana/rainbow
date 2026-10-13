(ns rainbow.algorithms.reference.coin-change
  "Executable coin-change min-DP, matching the proved Rainbow cell rule.")

(defn cell [current-best candidate]
  (if (<= candidate current-best) candidate current-best))

(defn min-coins
  "Minimum coins to make amount from denominations, or nil if impossible."
  [amount coins]
  (let [inf 1e18
        dp (reduce
            (fn [dp a]
              (assoc dp a
                     (reduce (fn [best c]
                               (if (>= a c) (cell best (+ 1 (dp (- a c)))) best))
                             inf coins)))
            (assoc (vec (repeat (inc amount) inf)) 0 0)
            (range 1 (inc amount)))]
    (when (< (dp amount) inf) (dp amount))))
