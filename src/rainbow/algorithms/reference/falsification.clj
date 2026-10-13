(ns rainbow.algorithms.reference.falsification
  "Executable Direct Sampling Falsification (AHoF V9). The falsification test
  matches the proved Rainbow definition; `falsify` samples inputs, evaluates
  their robustness, and returns the first counterexample at or below the margin.")

(defn falsifies?
  "A sample falsifies the spec when its robustness margin is at most the
  threshold."
  [robustness margin]
  (<= robustness margin))

(defn falsify
  "Return the first sampled input whose robustness falsifies the spec, or nil if
  none of the `samples` does. `robustness-of` maps an input to its robustness."
  [robustness-of margin samples]
  (first (filter #(falsifies? (robustness-of %) margin) samples)))
