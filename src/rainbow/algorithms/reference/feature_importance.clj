(ns rainbow.algorithms.reference.feature-importance
  "Executable exact-rational Permutation Feature Importance (AHoF V54). The score
  drop matches the proved Rainbow definition; the scoring model, the permutation,
  and the averaging over repetitions are the executable concern."
  (:refer-clojure :exclude []))

(defn importance
  "importance = baseline-score - permuted-score."
  [baseline permuted]
  (- baseline permuted))

(defn mean-importance
  "Average importance over repeated permutations."
  [baseline permuted-scores]
  (/ (reduce + (map #(importance baseline %) permuted-scores))
     (count permuted-scores)))
