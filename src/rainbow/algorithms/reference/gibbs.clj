(ns rainbow.algorithms.reference.gibbs
  "Executable Gibbs full-conditional draw via inverse-transform sampling on the
  conditional CDF (the prefix-sum scan)."
  (:require [rainbow.algorithms.reference.prefix-sum :as prefix-sum]))

(defn conditional-cdf
  "Conditional CDF for a full-conditional probability vector."
  [conditional-probs]
  (prefix-sum/cumulative-sum conditional-probs))

(defn draw-index
  "Index drawn from the full conditional given a uniform draw u in [0,1)."
  [conditional-probs u]
  (let [cdf (conditional-cdf conditional-probs)]
    (or (first (keep-indexed (fn [i c] (when (<= u c) i)) cdf))
        (dec (count conditional-probs)))))
