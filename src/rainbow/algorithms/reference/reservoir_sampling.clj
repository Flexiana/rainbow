(ns rainbow.algorithms.reference.reservoir-sampling
  "Executable reservoir sampling (Algorithm R), matching the proved rule.")

(defn replaces? [slot k] (<= slot k))

(defn sample
  "Reservoir sample of size k from a stream, using a supplied rng (i -> slot in
  [1,i]) for determinism. Returns the reservoir."
  [k stream rng]
  (loop [items (map vector (map inc (range)) stream), res []]
    (if (empty? items)
      res
      (let [[i x] (first items)]
        (cond
          (<= i k) (recur (rest items) (conj res x))
          :else (let [j (rng i)]
                  (recur (rest items)
                         (if (replaces? j k) (assoc res (dec j) x) res))))))))
