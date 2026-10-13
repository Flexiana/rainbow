(ns rainbow.algorithms.reference.fenwick-tree
  "Executable Fenwick tree (BIT), matching the proved additive accumulate.")

(defn accumulate [partial node-value] (+ partial node-value))

(defn- low-bit [i] (bit-and i (- i)))

(defn build [n] (vec (repeat (inc n) 0)))

(defn update-point
  "Add delta at 1-indexed position i."
  [tree i delta]
  (loop [tree tree, i i]
    (if (>= i (count tree))
      tree
      (recur (update tree i accumulate delta) (+ i (low-bit i))))))

(defn prefix-sum
  "Sum of the first i elements (1-indexed)."
  [tree i]
  (loop [i i, acc 0]
    (if (<= i 0)
      acc
      (recur (- i (low-bit i)) (accumulate acc (tree i))))))

(defn range-sum [tree l r] (- (prefix-sum tree r) (prefix-sum tree (dec l))))
