(ns rainbow.algorithms.reference.simplex
  "Executable exact-rational Simplex min-ratio test (AHoF O54). The pairwise pivot
  ratio matches the proved Rainbow definition; `leaving-row` runs the full
  minimum-ratio test over a tableau column, ignoring non-positive entries.")

(defn pivot-ratio
  "The winning ratio of two candidate rows: the smaller."
  [r1 r2]
  (min r1 r2))

(defn leaving-row
  "Minimum-ratio test: among rows with positive pivot-column entry, return the
  index of the one with the smallest rhs/entry ratio (the leaving variable), or
  nil if the column is unbounded. `rhs` and `column` are aligned vectors."
  [rhs column]
  (let [ratios (keep-indexed
                (fn [i a] (when (pos? a) [i (/ (nth rhs i) a)]))
                column)]
    (when (seq ratios)
      (first (apply min-key second ratios)))))
