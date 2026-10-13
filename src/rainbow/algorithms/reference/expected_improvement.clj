(ns rainbow.algorithms.reference.expected-improvement
  "Executable exact-rational Expected Improvement acquisition (AHoF O63). The
  acquisition matches the proved Rainbow definition; `select` picks the candidate
  maximizing EI over supplied surrogate predictions.")

(defn ei
  "improvement*prob + uncertainty*density."
  [improvement prob uncertainty density]
  (+ (* improvement prob) (* uncertainty density)))

(defn select
  "Choose the candidate with the highest expected improvement. `stats` maps a
  candidate to [improvement prob uncertainty density]."
  [stats candidates]
  (apply max-key
         (fn [c] (apply ei (stats c)))
         candidates))
