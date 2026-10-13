(ns rainbow.algorithms.reference.cross-entropy
  "Executable exact-rational Cross-Entropy Method (AHoF O41). The elite test
  matches the proved Rainbow definition; `elite-set` selects the top fraction of
  a scored population by the quantile threshold.")

(defn elite?
  "A sample is elite when its score reaches the threshold (maximization)."
  [score threshold]
  (<= threshold score))

(defn elite-threshold
  "The rho-quantile score: keep the top `rho` fraction of the population."
  [scores rho]
  (let [sorted (sort > scores)
        k (max 1 (int (* rho (count scores))))]
    (nth sorted (dec k))))

(defn elite-set
  "The elite samples: those scoring at or above the rho-quantile threshold."
  [scored rho]
  (let [threshold (elite-threshold (map second scored) rho)]
    (filter (fn [[_ s]] (elite? s threshold)) scored)))
