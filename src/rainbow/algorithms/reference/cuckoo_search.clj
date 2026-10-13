(ns rainbow.algorithms.reference.cuckoo-search
  "Executable exact-rational Cuckoo Search (AHoF O47). The Levy-flight step
  matches the proved Rainbow definition; nest abandonment (keep the better of the
  new candidate and a random nest) is the executable selector."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn levy-step
  "position' = position + rate * direction."
  [position rate direction]
  (vector/add position (vector/scale rate direction)))

(defn abandon
  "Replace a nest only when the candidate improves the objective, else keep it."
  [objective nest candidate]
  (if (< (objective candidate) (objective nest)) candidate nest))
