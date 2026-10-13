(ns rainbow.algorithms.reference.astar
  "Executable exact-rational A* search (AHoF D37). The f-value matches the proved
  Rainbow definition; `search` runs best-first search expanding the least-f
  frontier node, with pluggable successor, heuristic, and goal functions.")

(defn f-value
  "Priority of a node: path cost so far plus heuristic estimate to go."
  [g h]
  (+ g h))

(defn search
  "A* from `start`. `successors` maps a node to [[next step-cost] ...]; `heuristic`
  estimates cost-to-go; `goal?` tests the goal. Returns the optimal path cost, or
  nil if unreachable."
  [start successors heuristic goal?]
  (loop [frontier {start 0} visited {}]
    (if (empty? frontier)
      nil
      (let [[node g] (apply min-key (fn [[n g]] (f-value g (heuristic n))) frontier)
            frontier (dissoc frontier node)]
        (cond
          (goal? node) g
          (and (visited node) (<= (visited node) g)) (recur frontier visited)
          :else
          (recur (reduce (fn [fr [nxt c]]
                           (let [ng (+ g c)]
                             (if (and (fr nxt) (<= (fr nxt) ng))
                               fr
                               (assoc fr nxt ng))))
                         frontier (successors node))
                 (assoc visited node g)))))))
