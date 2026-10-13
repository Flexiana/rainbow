(ns rainbow.algorithms.reference.variable-elimination
  "Executable exact-rational Variable Elimination (AHoF D3). Binary
  marginalization matches the proved Rainbow definition; `eliminate` sums a
  factor over all values of a variable, and `infer` eliminates a whole ordering.")

(defn marginalize
  "Sum the two slices of a binary variable."
  [f-false f-true]
  (+ f-false f-true))

(defn eliminate
  "Marginalize a factor (a map from assignment -> value) over variable `v`:
  group by the remaining assignment and sum over v's values."
  [factor v]
  (reduce (fn [acc [assignment value]]
            (update acc (dissoc assignment v) (fnil + 0) value))
          {}
          factor))
