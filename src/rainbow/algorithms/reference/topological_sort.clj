(ns rainbow.algorithms.reference.topological-sort
  "Executable Kahn's topological sort, matching the proved Rainbow readiness
  rule.")

(defn ready? [in-degree] (<= in-degree 0))

(defn topological-sort
  "Kahn's algorithm: a topological order of a DAG given adjacency (node -> succs)
  and the node set. Returns nil if the graph has a cycle."
  [nodes adjacency]
  (let [indeg (reduce (fn [m n]
                        (reduce (fn [m s] (update m s (fnil inc 0)))
                                m (adjacency n)))
                      (zipmap nodes (repeat 0)) nodes)]
    (loop [indeg indeg, ready (filterv #(ready? (indeg %)) nodes), order []]
      (if (empty? ready)
        (when (= (count order) (count nodes)) order)
        (let [n (first ready)
              indeg' (reduce (fn [m s] (update m s dec)) indeg (adjacency n))
              newly (filterv #(and (ready? (indeg' %))
                                   (not (ready? (indeg %)))) (adjacency n))]
          (recur indeg' (into (subvec ready 1) newly) (conj order n)))))))
