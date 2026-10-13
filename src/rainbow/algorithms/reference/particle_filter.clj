(ns rainbow.algorithms.reference.particle-filter
  "Executable particle-filter systematic resampling via inverse-transform
  sampling on the cumulative weight distribution (the prefix-sum scan)."
  (:require [rainbow.algorithms.reference.prefix-sum :as prefix-sum]))

(defn weight-cdf
  "Cumulative weight distribution for a particle weight vector."
  [weights]
  (prefix-sum/cumulative-sum weights))

(defn resample-index
  "Index of the particle resampled for a draw u in [0, total-weight)."
  [weights u]
  (let [cdf (weight-cdf weights)]
    (or (first (keep-indexed (fn [i c] (when (<= u c) i)) cdf))
        (dec (count weights)))))
