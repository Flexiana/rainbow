(ns rainbow.algorithms.reference.tsp-nearest-neighbor
  "Executable nearest-neighbor TSP, matching the proved Rainbow selection.")

(defn nearer-city [da na db nb] (if (<= da db) na nb))

(defn tour
  "Nearest-neighbor tour from city 0 given a distance matrix (vector of vectors).
  Returns [tour total-distance]."
  [dist]
  (let [n (count dist)]
    (loop [cur 0, visited #{0}, path [0], total 0]
      (if (= (count visited) n)
        [(conj path 0) (+ total ((dist cur) 0))]
        (let [cands (remove visited (range n))
              nxt (reduce (fn [a b] (nearer-city ((dist cur) a) a ((dist cur) b) b))
                          (first cands) (rest cands))]
          (recur nxt (conj visited nxt) (conj path nxt)
                 (+ total ((dist cur) nxt))))))))
