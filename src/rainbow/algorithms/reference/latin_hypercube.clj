(ns rainbow.algorithms.reference.latin-hypercube
  "Executable Latin Hypercube Sampling design (AHoF O59). The sampling-cost
  counts match the proved Rainbow definitions; `design` realizes a concrete LHS
  by assigning, per dimension, a permutation of the n stratum indices, so each
  stratum is used exactly once along every axis.")

(defn sample-count
  "Number of objective evaluations: n, independent of the dimension count."
  [n _k]
  n)

(defn total-strata
  "Total stratum cells across all dimensions: n strata in each of k dimensions."
  [n k]
  (* n k))

(defn design
  "An LHS design as n points in k dimensions. `permute` maps a dimension index
  to a permutation (vector) of the stratum indices 0..n-1; point i takes stratum
  (permute d)[i] in dimension d. Each stratum index appears exactly once per
  dimension (the Latin property)."
  [n k permute]
  (let [columns (mapv (fn [d] (permute d)) (range k))]
    (mapv (fn [i] (mapv (fn [col] (nth col i)) columns))
          (range n))))
