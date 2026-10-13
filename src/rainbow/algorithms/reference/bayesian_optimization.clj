(ns rainbow.algorithms.reference.bayesian-optimization
  "Executable exact-rational Bayesian Optimization loop (AHoF O65). The incumbent
  update matches the proved Rainbow definition; `optimize` runs the fit ->
  acquire -> evaluate loop, tracking the best observation.")

(defn update-incumbent
  "Keep the better of the incumbent and the newly evaluated candidate."
  [best candidate]
  (max best candidate))

(defn optimize
  "Run `iterations` of Bayesian optimization. `select` proposes the next point
  from the observations so far (fit surrogate + maximize acquisition, pluggable);
  `evaluate` scores a point. Returns the best value found."
  [select evaluate initial-points iterations]
  (loop [observations (mapv (fn [p] [p (evaluate p)]) initial-points)
         best (reduce max (map second observations))
         remaining iterations]
    (if (zero? remaining)
      best
      (let [next-point (select observations)
            value (evaluate next-point)]
        (recur (conj observations [next-point value])
               (update-incumbent best value)
               (dec remaining))))))
