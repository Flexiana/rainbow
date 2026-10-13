(ns rainbow.algorithms.reference.argmax-index
  "Executable argmax-index, matching the proved Rainbow definition: index of the
  maximum element, ties to the earliest.")

(defn argmax-index
  "Index of the maximum of xs (earliest on ties)."
  [xs]
  (first (reduce (fn [[bi bv] [i v]] (if (> v bv) [i v] [bi bv]))
                 [0 (first xs)]
                 (map-indexed vector xs))))
