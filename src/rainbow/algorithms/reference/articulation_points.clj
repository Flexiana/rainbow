(ns rainbow.algorithms.reference.articulation-points
  "Executable articulation points (Tarjan low-link), matching the proved cut-vertex
  decision.")

(defn is-articulation? [disc-u child-low] (<= disc-u child-low))

(defn articulation-points
  "Set of articulation points of an undirected graph (adjacency node -> neighbor
  set)."
  [nodes adj]
  (let [state (atom {:timer 0 :disc {} :low {} :aps #{}})]
    (letfn [(dfs [u parent]
              (swap! state (fn [s] (-> s (update :timer inc)
                                       (assoc-in [:disc u] (:timer s))
                                       (assoc-in [:low u] (:timer s)))))
              (let [children (atom 0)]
                (doseq [v (adj u) :when (not= v parent)]
                  (if (get-in @state [:disc v])
                    (swap! state update-in [:low u] min (get-in @state [:disc v]))
                    (do
                      (swap! children inc)
                      (dfs v u)
                      (swap! state update-in [:low u] min (get-in @state [:low v]))
                      (when (and (some? parent)
                                 (is-articulation? (get-in @state [:disc u])
                                                   (get-in @state [:low v])))
                        (swap! state update :aps conj u)))))
                (when (and (nil? parent) (> @children 1))
                  (swap! state update :aps conj u))))]
      (doseq [u nodes :when (not (get-in @state [:disc u]))] (dfs u nil))
      (:aps @state))))
