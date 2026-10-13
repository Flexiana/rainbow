(ns rainbow.algorithms.reference.simplex-interpolation
  "Executable exact-rational Simplex Interpolation (AHoF D28). The barycentric
  combination matches the proved Rainbow definition; `interpolate` generalizes to
  any simplex as the weighted sum of vertex values by barycentric coordinates.")

(defn interpolate-tri [l1 v1 l2 v2 l3 v3]
  (+ (* l1 v1) (* l2 v2) (* l3 v3)))

(defn interpolate
  "Barycentric interpolation: sum of barycentric weights * vertex values."
  [lambdas vertex-values]
  (reduce + 0 (map * lambdas vertex-values)))
