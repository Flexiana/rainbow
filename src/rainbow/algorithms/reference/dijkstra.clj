(ns rainbow.algorithms.reference.dijkstra
  "Executable Dijkstra shortest paths, matching the proved selection rule.")

(defn closer-vertex [da na db nb] (if (<= da db) na nb))

(defn shortest-paths
  "Dijkstra from source s. adjacency: node -> [[neighbor weight] ...]."
  [n adjacency s]
  (let [inf 1e18]
    (loop [dist (assoc (vec (repeat n inf)) s 0), done #{}]
      (let [frontier (remove done (range n))]
        (if (empty? frontier)
          dist
          (let [u (reduce (fn [a b] (closer-vertex (dist a) a (dist b) b))
                          (first frontier) (rest frontier))]
            (if (>= (dist u) inf)
              dist
              (recur (reduce (fn [d [v w]]
                               (let [cand (+ (dist u) w)]
                                 (if (< cand (d v)) (assoc d v cand) d)))
                             dist (adjacency u))
                     (conj done u)))))))))
