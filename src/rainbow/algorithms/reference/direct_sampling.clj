(ns rainbow.algorithms.reference.direct-sampling
  "Executable exact-rational Direct Sampling (AHoF D5). The selection test matches
  the proved Rainbow definition; `sample-categorical` draws a category by
  inverse-transform sampling of a categorical distribution.")

(defn selects? [cumulative u] (<= u cumulative))

(defn sample-categorical
  "Inverse-transform draw: return the first category whose running cumulative
  probability reaches the uniform draw `u`. `probs` is a seq of [category prob]."
  [probs u]
  (loop [cumulative 0 remaining probs]
    (when (seq remaining)
      (let [[category p] (first remaining)
            cumulative (+ cumulative p)]
        (if (selects? cumulative u)
          category
          (recur cumulative (rest remaining)))))))
