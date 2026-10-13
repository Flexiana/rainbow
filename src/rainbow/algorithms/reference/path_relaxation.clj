(ns rainbow.algorithms.reference.path-relaxation
  "Executable exact-rational shortest-path relaxation (Bellman-Ford / Dijkstra
  core). The pairwise relaxation matches the proved Rainbow definition;
  `bellman-ford` runs single-source shortest paths by relaxing every edge until
  distances settle.")

(defn relax
  "Keep the shorter of the current tentative distance and a candidate."
  [current alt]
  (min current alt))

(defn relax-all
  "Relax `current` against several candidate distances."
  [current alts]
  (reduce relax current alts))

(defn bellman-ford
  "Single-source shortest distances. `nodes` is the node set; `edges` is a seq of
  [from to weight]; `source` starts at 0, all others at infinity. Relaxes every
  edge |nodes|-1 times."
  [nodes edges source]
  (let [init (into {} (map (fn [n] [n (if (= n source) 0 Double/POSITIVE_INFINITY)])
                           nodes))]
    (reduce (fn [dist _]
              (reduce (fn [d [from to weight]]
                        (let [alt (+ (d from) weight)]
                          (update d to relax alt)))
                      dist edges))
            init
            (range (dec (count nodes))))))
