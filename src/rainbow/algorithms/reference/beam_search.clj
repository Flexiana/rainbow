(ns rainbow.algorithms.reference.beam-search
  "Executable beam search pruning, matching the proved Rainbow definition.")

(defn in-beam? [score cutoff] (<= cutoff score))

(defn beam
  "Top-k candidates by score (the beam) from [candidate score] pairs."
  [k candidates]
  (take k (sort-by (comp - second) candidates)))
