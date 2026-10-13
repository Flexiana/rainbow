(ns rainbow.algorithms.reference.rejection-sampling
  "Executable Rejection Sampling (AHoF V21). The acceptance test matches the
  proved Rainbow definition; `sample` retains the consistent draws and reports
  the acceptance ratio.")

(defn accepts?
  "A sample is accepted when its statistic is within the evidence tolerance."
  [statistic tolerance]
  (<= statistic tolerance))

(defn sample
  "Rejection-sample: keep the draws whose statistic is within tolerance."
  [statistic-of tolerance draws]
  (filter #(accepts? (statistic-of %) tolerance) draws))

(defn acceptance-ratio
  "Fraction of draws retained (the sampling efficiency)."
  [statistic-of tolerance draws]
  (if (empty? draws)
    0
    (/ (count (sample statistic-of tolerance draws)) (count draws))))
