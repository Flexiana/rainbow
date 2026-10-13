(ns rainbow.algorithms.reference.fuzzing
  "Executable Fuzzing (AHoF V11). The bit-flip mutation matches the proved Rainbow
  definition; `fuzz` iterates mutations of a seed and returns the first mutant
  that violates the specification.")

(defn flip
  "Toggle a boolean bit."
  [b]
  (not b))

(defn mutate
  "Flip the bit at index i of a boolean input vector."
  [input i]
  (update (vec input) i flip))

(defn fuzz
  "Search single-bit mutations of `seed` for one violating `spec?`. Returns the
  first violating mutant, or nil if all single-bit mutants satisfy the spec."
  [spec? seed]
  (first (remove spec?
                 (map #(mutate seed %) (range (count seed))))))
