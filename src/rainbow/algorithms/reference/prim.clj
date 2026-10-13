(ns rainbow.algorithms.reference.prim
  "Executable Prim's MST, matching the proved Rainbow selection rule.")

(defn lighter-edge
  "Endpoint of the lighter of two crossing edges."
  [wa ea wb eb]
  (if (<= wa wb) ea eb))

(defn mst-weight
  "Total weight of Prim's MST from vertex 0, given a symmetric weight map
  {[u v] w}. n = number of vertices."
  [n weights]
  (loop [in #{0}, total 0]
    (if (= (count in) n)
      total
      (let [crossing (for [u in v (range n)
                           :when (and (not (in v)) (weights [u v]))]
                       [(weights [u v]) v])
            [w v] (first (sort crossing))]
        (recur (conj in v) (+ total w))))))
