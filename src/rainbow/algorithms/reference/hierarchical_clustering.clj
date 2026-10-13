(ns rainbow.algorithms.reference.hierarchical-clustering
  "Executable agglomerative clustering (single linkage), matching the proved
  closest-pair rule.")

(defn closest-pair [dab pab dcd pcd] (if (<= dab dcd) pab pcd))

(defn cluster
  "Single-linkage agglomerative clustering of 1-D points. Returns the merge
  sequence [cluster-a cluster-b distance]."
  [points]
  (let [dist (fn [a b] (apply min (for [x a y b] (abs (- x y)))))]
    (loop [clusters (mapv vector points), merges []]
      (if (<= (count clusters) 1)
        merges
        (let [pairs (for [i (range (count clusters))
                          j (range (inc i) (count clusters))]
                      [(dist (clusters i) (clusters j)) i j])
              [d i j] (reduce (fn [[da _ _ :as pa] [db _ _ :as pb]]
                               (if (closest-pair da 0 db 1) pa pb))
                             pairs)]
          (recur (conj (vec (keep-indexed
                             #(when-not (#{i j} %1) %2) clusters))
                       (into (clusters i) (clusters j)))
                 (conj merges [i j d])))))))
