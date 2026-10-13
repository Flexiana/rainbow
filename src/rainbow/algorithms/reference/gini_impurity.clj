(ns rainbow.algorithms.reference.gini-impurity
  "Executable Gini impurity, matching the proved purity comparison.")

(defn purer-split? [impurity-a impurity-b] (<= impurity-a impurity-b))

(defn gini
  "Gini impurity 1 - sum p_i^2 from class counts."
  [counts]
  (let [n (reduce + counts)]
    (if (zero? n)
      0
      (- 1 (reduce + (map (fn [c] (let [p (/ c n)] (* p p))) counts))))))

(defn best-split
  "Index of the purer (lower-Gini) split among candidate class-count vectors."
  [candidate-counts]
  (first (apply min-key second (map-indexed (fn [i c] [i (gini c)])
                                            candidate-counts))))
