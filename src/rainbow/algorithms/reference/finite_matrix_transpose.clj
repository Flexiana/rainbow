(ns rainbow.algorithms.reference.finite-matrix-transpose
  "Executable reference semantics for native row-major matrix transpose.")

(defn prepend-column
  "Insert `values` down the fronts of `columns`.

  The result width is exactly the length of `values`: absent columns become
  singleton vectors and surplus columns are dropped."
  [values columns]
  (loop [remaining-values (seq values)
         remaining-columns (seq columns)
         result []]
    (if remaining-values
      (recur (next remaining-values)
             (next remaining-columns)
             (conj result
                   (into [(first remaining-values)]
                         (or (first remaining-columns) []))))
      result)))

(defn transpose
  "Transpose rows by folding `prepend-column` from the final row upward.

  On rectangular matrices this is standard transpose. On ragged matrices the
  first row determines the final width, matching the proved total definition."
  [rows]
  (if-let [current-rows (seq rows)]
    (prepend-column (first current-rows)
                    (transpose (next current-rows)))
    []))
