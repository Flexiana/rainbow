(ns rainbow.algorithms.reference.conformal
  "Executable conformal prediction, matching the proved Rainbow definition.")

(defn in-prediction-set?
  "True iff a label's nonconformity score is within the threshold q."
  [score q]
  (<= score q))

(defn empirical-quantile
  "The conformal threshold: the ceil((n+1)(1-alpha))-th smallest calibration
  score (finite-sample-adjusted (1-alpha) quantile)."
  [calibration-scores alpha]
  (let [sorted (vec (sort calibration-scores))
        n (count sorted)
        k (min n (long (Math/ceil (* (+ n 1) (- 1 alpha)))))]
    (nth sorted (dec (max 1 k)))))

(defn prediction-set
  "Labels whose score is within the threshold."
  [candidate->score labels q]
  (set (filter #(in-prediction-set? (candidate->score %) q) labels)))
