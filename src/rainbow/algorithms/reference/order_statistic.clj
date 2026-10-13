(ns rainbow.algorithms.reference.order-statistic
  "Executable empirical rank / order statistics (AHoF). The threshold count
  matches the proved Rainbow definition; the derived functions realize the
  empirical CDF and quantile lookups the count underlies.")

(defn count-at-most
  "Number of sample values at or below the threshold."
  [threshold xs]
  (count (filter #(<= % threshold) xs)))

(defn empirical-cdf
  "Empirical CDF value at the threshold: fraction of samples at or below it."
  [threshold xs]
  (if (empty? xs)
    0
    (/ (count-at-most threshold xs) (count xs))))

(defn rank
  "1-based rank of x among the sorted samples (number of values <= x)."
  [x xs]
  (count-at-most x xs))
