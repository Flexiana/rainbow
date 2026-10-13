(ns rainbow.algorithms.reference.network-scoring
  "Executable exact-rational additive Bayesian-network scoring. The network score
  is the sum of a per-node local score over the nodes -- a map followed by a
  reduce. Because the score decomposes additively, adding a node adds only its
  local score. Matches the proved Rainbow definition.")

(defn total-score
  "Sum the local score over the nodes."
  [local-score nodes]
  (reduce + 0 (map local-score nodes)))

(defn add-node-delta
  "The exact change in score from adding a node is its local score."
  [local-score node]
  (local-score node))
