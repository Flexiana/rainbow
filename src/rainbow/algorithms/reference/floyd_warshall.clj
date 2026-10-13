(ns rainbow.algorithms.reference.floyd-warshall
  "Executable exact-rational Floyd-Warshall all-pairs shortest paths (AHoF). The
  relaxation cell matches the proved Rainbow definition; `all-pairs` fills the
  full distance matrix by the triple loop over intermediate nodes.")

(defn cell
  "Relax i->j through k: the better of the direct estimate and the detour."
  [direct dik dkj]
  (min direct (+ dik dkj)))

(defn all-pairs
  "All-pairs shortest distances. `dist` is a map {[i j] w} of edge weights;
  `nodes` the node set. Missing pairs start at infinity, diagonal at 0."
  [nodes dist]
  (let [inf Double/POSITIVE_INFINITY
        init (into {} (for [i nodes j nodes]
                        [[i j] (cond (= i j) 0
                                     (contains? dist [i j]) (dist [i j])
                                     :else inf)]))]
    (reduce
     (fn [d k]
       (into {} (for [i nodes j nodes]
                  [[i j] (cell (d [i j]) (d [i k]) (d [k j]))])))
     init
     nodes)))
