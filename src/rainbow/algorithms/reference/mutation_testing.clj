(ns rainbow.algorithms.reference.mutation-testing
  "Executable mutation-testing score and adequacy, matching the proved Rainbow
  definitions.")

(defn mutation-score
  "Fraction of mutants killed."
  [killed total]
  (/ killed total))

(defn adequate?
  "True iff the mutation score meets the target threshold."
  [score threshold]
  (<= threshold score))

(defn suite-adequate?
  "Run adequacy directly from killed/total counts."
  [killed total threshold]
  (adequate? (mutation-score killed total) threshold))
