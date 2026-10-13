(ns rainbow.algorithms.reference.decision-tree
  "Executable greedy decision-tree split selection, matching the proved Rainbow
  definitions.")

(defn choose-split
  "Feature index of the higher-gain split between two candidates."
  [ga fa gb fb]
  (if (<= ga gb) fb fa))

(defn is-leaf?
  "True iff the best available gain does not exceed the minimum-gain threshold."
  [best-gain min-gain]
  (<= best-gain min-gain))

(defn best-split
  "Best (feature, gain) over candidate [feature gain] pairs."
  [candidates]
  (apply max-key second candidates))
