(ns rainbow.algorithms.reference.kosaraju
  "Executable Kosaraju SCC, matching the proved mutual-reachability membership.")

(defn same-scc? [u-reaches-v? v-reaches-u?] (and u-reaches-v? v-reaches-u?))

(defn- reachable [adj start]
  (loop [stack [start], seen #{}]
    (if (empty? stack)
      seen
      (let [v (peek stack)]
        (if (seen v)
          (recur (pop stack) seen)
          (recur (into (pop stack) (adj v)) (conj seen v)))))))

(defn sccs
  "Strongly connected components of a directed graph (adjacency node -> succs)."
  [nodes adj]
  (let [radj (reduce (fn [m [u vs]] (reduce #(update %1 %2 (fnil conj #{}) u) m vs))
                     (zipmap nodes (repeat #{})) adj)
        fwd (into {} (map (fn [n] [n (reachable adj n)]) nodes))
        bwd (into {} (map (fn [n] [n (reachable radj n)]) nodes))]
    (->> nodes
         (group-by (fn [v] (set (filter #(same-scc? (contains? (fwd v) %)
                                                    (contains? (bwd v) %))
                                        nodes))))
         vals (map set) set)))
