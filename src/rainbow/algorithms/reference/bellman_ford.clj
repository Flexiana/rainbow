(ns rainbow.algorithms.reference.bellman-ford
  "Executable Bellman-Ford shortest paths, matching the proved relaxation rule.")

(defn relaxes? [candidate current] (<= candidate current))

(defn shortest-paths
  "Bellman-Ford from source s. edges are [u v w]. Returns dist map, or
  :negative-cycle if one is reachable. inf is a large sentinel."
  [n edges s]
  (let [inf 1e18
        init (assoc (vec (repeat n inf)) s 0)
        relax (fn [dist]
                (reduce (fn [d [u v w]]
                          (let [cand (+ (d u) w)]
                            (if (relaxes? cand (d v)) (assoc d v cand) d)))
                        dist edges))
        dist (nth (iterate relax init) (dec n))
        once-more (relax dist)]
    (if (= once-more dist) dist :negative-cycle)))
