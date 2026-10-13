(ns rainbow.algorithms.reference.gradient-clipping
  "Executable gradient clipping (clip-by-norm), matching the proved Rainbow
  decision.")

(defn clips? [grad-norm threshold] (<= threshold grad-norm))

(defn clip
  "Clip a gradient vector to the threshold norm (preserving direction)."
  [gradient threshold]
  (let [norm (Math/sqrt (reduce + (map #(* % %) gradient)))]
    (if (clips? norm threshold)
      (mapv #(* % (/ threshold norm)) gradient)
      (vec gradient))))
