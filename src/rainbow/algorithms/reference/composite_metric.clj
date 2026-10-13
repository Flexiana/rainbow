(ns rainbow.algorithms.reference.composite-metric
  "Executable exact-rational composite evaluation metric: a weighted combination
  of two atomic metrics, `w1 * m1 + w2 * m2`. Matches the proved Rainbow
  definitions.")

(defn composite-metric
  "Weighted combination of two atomic metrics."
  [weight-a metric-a weight-b metric-b]
  (+ (* weight-a metric-a) (* weight-b metric-b)))
