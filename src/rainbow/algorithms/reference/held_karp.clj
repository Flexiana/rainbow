(ns rainbow.algorithms.reference.held-karp
  "Executable Held-Karp exact TSP (bitmask DP), matching the proved cell rules.")

(defn path-cost [subpath edge] (+ subpath edge))
(defn better [current-best candidate]
  (if (<= candidate current-best) candidate current-best))

(defn tsp
  "Minimum Hamiltonian-cycle cost over a distance matrix, starting/ending at 0."
  [dist]
  (let [n (count dist), full (dec (bit-shift-left 1 n)), inf 1e18
        dp (atom {})]
    (swap! dp assoc [1 0] 0)             ; start at city 0, only 0 visited
    (doseq [s (range 1 (inc full)) :when (bit-test s 0)
            j (range n) :when (bit-test s j)]
      (when (and (not= s 1) (pos? j))
        (let [prev (bit-clear s j)]
          (swap! dp assoc [s j]
                 (reduce (fn [best k]
                           (if (bit-test prev k)
                             (better best (path-cost (get @dp [prev k] inf)
                                                     ((dist k) j)))
                             best))
                         inf (range n))))))
    (reduce (fn [best j]
              (if (pos? j)
                (better best (path-cost (get @dp [full j] inf) ((dist j) 0)))
                best))
            inf (range n))))
