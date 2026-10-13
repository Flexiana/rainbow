(ns rainbow.algorithms.reference.johnson
  "Executable Johnson all-pairs shortest paths, matching the proved reweight-
  non-negativity decision.")

(defn nonneg-reweighted? [reweighted-weight] (<= 0 reweighted-weight))

(def ^:private inf 1e18)

(defn- bellman-ford
  "Potentials h(v) from a virtual source connected to all vertices with 0-weight
  edges. edges: [u v w]."
  [n edges]
  (loop [h (vec (repeat n 0)), i 0]
    (if (= i n)
      h
      (recur (reduce (fn [h [u v w]]
                       (if (< (+ (h u) w) (h v)) (assoc h v (+ (h u) w)) h))
                     h edges)
             (inc i)))))

(defn- dijkstra [n adj s]
  (loop [dist (assoc (vec (repeat n inf)) s 0), done #{}]
    (let [u (->> (range n) (remove done) (sort-by dist) first)]
      (if (or (nil? u) (>= (dist u) inf))
        dist
        (recur (reduce (fn [d [v w]]
                         (if (< (+ (dist u) w) (d v)) (assoc d v (+ (dist u) w)) d))
                       dist (adj u))
               (conj done u))))))

(defn all-pairs
  "All-pairs shortest distances via Johnson's algorithm. edges: [u v w]."
  [n edges]
  (let [h (bellman-ford n edges)
        radj (reduce (fn [m [u v w]]
                       (let [rw (+ w (h u) (- (h v)))]
                         (assert (nonneg-reweighted? rw))
                         (update m u (fnil conj []) [v rw])))
                     {} edges)
        adj (fn [u] (get radj u []))]
    (vec (for [s (range n)]
           (let [d (dijkstra n adj s)]
             (mapv (fn [v] (if (>= (d v) inf) inf (+ (d v) (h v) (- (h s)))))
                   (range n)))))))
