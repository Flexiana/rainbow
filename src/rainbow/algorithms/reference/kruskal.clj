(ns rainbow.algorithms.reference.kruskal
  "Executable Kruskal's MST, matching the proved Rainbow acceptance rule."
  (:require [rainbow.algorithms.reference.union-find :as uf]))

(defn accepts-edge?
  "True iff an edge's endpoint representatives are in different components."
  [ra rb]
  (not (uf/connected? ra rb)))

(defn mst
  "Kruskal's MST edges from weighted edges [w u v], with n vertices."
  [n edges]
  (let [sorted (sort-by first edges)]
    (loop [parent (vec (range n)), es sorted, tree []]
      (if (empty? es)
        tree
        (let [[w u v] (first es)
              ru (uf/find-rep parent u), rv (uf/find-rep parent v)]
          (if (accepts-edge? ru rv)
            (recur (assoc parent ru rv) (rest es) (conj tree [w u v]))
            (recur parent (rest es) tree)))))))
