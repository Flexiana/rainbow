(ns rainbow.algorithms.reference.gas-station
  "Executable gas-station greedy, matching the proved feasibility decision.")

(defn can-complete? [total-gas total-cost] (<= total-cost total-gas))

(defn start-station
  "Index of a valid starting station for the circular tour, or -1 if impossible."
  [gas cost]
  (if-not (can-complete? (reduce + gas) (reduce + cost))
    -1
    (loop [i 0, start 0, tank 0]
      (if (>= i (count gas))
        start
        (let [tank (+ tank (- (gas i) (cost i)))]
          (if (neg? tank)
            (recur (inc i) (inc i) 0)
            (recur (inc i) start tank)))))))
