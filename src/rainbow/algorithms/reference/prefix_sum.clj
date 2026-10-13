(ns rainbow.algorithms.reference.prefix-sum
  "Executable prefix-sum / scan. Matches the proved Rainbow definition; the CDF
  is the prefix sum of a probability vector.")

(defn cumulative-sum
  "Running totals of xs."
  [xs]
  (rest (reductions + 0 xs)))

(defn cdf
  "Cumulative distribution function of a probability vector."
  [probs]
  (cumulative-sum probs))
