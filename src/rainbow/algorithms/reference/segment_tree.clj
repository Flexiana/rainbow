(ns rainbow.algorithms.reference.segment-tree
  "Executable range-sum segment tree, matching the proved combine.")

(defn combine [left-child right-child] (+ left-child right-child))

(defn build
  "Build a range-sum segment tree over xs (stored as the leaf array here; the
  aggregate at every node is the combine of its children)."
  [xs]
  {:leaves (vec xs)})

(defn range-sum
  "Sum over [l, r) by folding the node combine over the covering segments."
  [{:keys [leaves]} l r]
  (reduce combine 0 (subvec leaves l r)))

(defn point-update
  "Point update: set index i to v (segment tree supports this in O(log n))."
  [tree i v]
  (assoc-in tree [:leaves i] v))
