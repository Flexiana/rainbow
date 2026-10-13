(ns rainbow.algorithms.reference.dual-simplex
  "Executable dual-simplex ratio test, matching the proved Rainbow definition.")

(defn choose-entering
  "Index of the min-ratio column between two candidates."
  [ra ia rb ib]
  (if (<= ra rb) ia ib))

(defn ratio-test
  "Entering-column index by the dual ratio test over [ratio index] pairs."
  [candidates]
  (second (reduce (fn [[br bi] [r i]] (if (< r br) [r i] [br bi]))
                  (first candidates)
                  (rest candidates))))
