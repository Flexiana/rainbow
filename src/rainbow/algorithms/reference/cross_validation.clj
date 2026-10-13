(ns rainbow.algorithms.reference.cross-validation
  "Executable exact-rational k-fold cross-validation mean. The cross-validation
  estimate is the sum of the per-fold scores divided by the fold count. Matches
  the proved Rainbow definitions.")

(defn total
  "Sum of the per-fold scores."
  [scores]
  (reduce + 0 scores))

(defn mean
  "The cross-validation estimate: fold total over fold count."
  [scores count]
  (/ (total scores) count))
