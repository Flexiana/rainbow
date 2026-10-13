(ns rainbow.algorithms.reference.confidence-interval
  "Executable confidence interval, matching the proved Rainbow containment.")

(defn contains? [value lower upper]
  (and (<= lower value) (<= value upper)))

(defn interval
  "Symmetric confidence interval estimate +/- z*standard-error."
  [estimate z standard-error]
  (let [margin (* z standard-error)]
    [(- estimate margin) (+ estimate margin)]))

(defn covers?
  "Does the CI around estimate cover the true parameter?"
  [estimate z standard-error true-value]
  (let [[lo hi] (interval estimate z standard-error)]
    (contains? true-value lo hi)))
