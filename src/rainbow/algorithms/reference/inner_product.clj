(ns rainbow.algorithms.reference.inner-product
  "Executable exact-rational vector dot product (inner product). Matches the
  proved Rainbow definition: the sum of componentwise products.")

(defn dot
  "Inner product: sum of componentwise products (truncating at the shorter)."
  [left right]
  (reduce + 0 (map * left right)))

(defn cosine-numerator
  "The numerator of cosine similarity: the dot product of the two vectors."
  [left right]
  (dot left right))
