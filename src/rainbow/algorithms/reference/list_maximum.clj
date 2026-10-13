(ns rainbow.algorithms.reference.list-maximum
  "Executable maximum-of-list fold, matching the proved Rainbow definition.")

(defn nnrat-max [a b] (if (<= a b) b a))

(defn list-maximum
  "Maximum of xs (0 for the empty list), as the fold of nnrat-max from 0."
  [xs]
  (reduce nnrat-max 0 xs))
