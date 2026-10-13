(ns rainbow.algorithms.reference.pagerank
  "Executable PageRank power iteration, matching the proved Rainbow update.")

(defn pagerank-update [teleport damping incoming]
  (+ teleport (* damping incoming)))

(defn pagerank
  "PageRank via power iteration. out-links: node -> [nodes]. Returns rank vector."
  [n out-links damping iterations]
  (let [teleport (/ (- 1 damping) n)
        in-links (reduce (fn [m [u vs]] (reduce #(update %1 %2 conj u) m vs))
                         (zipmap (range n) (repeat [])) out-links)
        outdeg (fn [u] (count (out-links u)))]
    (nth (iterate
          (fn [pr]
            (mapv (fn [p]
                    (pagerank-update
                     teleport damping
                     (reduce (fn [s q] (+ s (/ (pr q) (outdeg q))))
                             0 (in-links p))))
                  (range n)))
          (vec (repeat n (/ 1 n))))
         iterations)))
