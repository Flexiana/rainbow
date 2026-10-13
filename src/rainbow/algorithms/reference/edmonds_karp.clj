(ns rainbow.algorithms.reference.edmonds-karp
  "Executable Edmonds-Karp max flow, matching the proved residual-capacity test.")

(defn has-residual? [residual] (<= 1 residual))

(defn- bfs-augment
  "Find a shortest augmenting path from s to t in the residual graph `cap`
  (map [u v] -> residual). Returns [path bottleneck] or nil."
  [cap n s t]
  (loop [queue [s], parent {s nil}]
    (if (empty? queue)
      nil
      (let [u (peek queue)]
        (if (= u t)
          (loop [v t, path ()]
            (if (nil? (parent v))
              (let [p (vec (cons v path))
                    b (apply min (map #(cap [%1 %2]) p (rest p)))]
                [p b])
              (recur (parent v) (cons v path))))
          (let [nbrs (for [v (range n)
                           :when (and (not (contains? parent v))
                                      (has-residual? (get cap [u v] 0)))]
                       v)]
            (recur (into (pop queue) nbrs)
                   (into parent (map (fn [v] [v u]) nbrs)))))))))

(defn max-flow
  "Maximum flow from s to t. edges: map [u v] -> capacity. n vertices."
  [edges n s t]
  (loop [cap (reduce (fn [m [[u v] c]] (-> m (update [u v] (fnil + 0) c)
                                           (update [v u] (fnil + 0) 0)))
                     {} edges)
         total 0]
    (if-let [[path b] (bfs-augment cap n s t)]
      (recur (reduce (fn [cap [u v]]
                       (-> cap (update [u v] - b) (update [v u] (fnil + 0) b)))
                     cap (map vector path (rest path)))
             (+ total b))
      total)))
