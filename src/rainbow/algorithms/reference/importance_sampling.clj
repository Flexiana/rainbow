(ns rainbow.algorithms.reference.importance-sampling
  "Executable exact-rational likelihood-weighted (importance) sampling estimate:
  the weight-weighted sum of the values divided by the total weight. Matches the
  proved Rainbow definitions.")

(defn weighted-sum
  "The weight-weighted sum of the sample values."
  [weight-a value-a weight-b value-b]
  (+ (* weight-a value-a) (* weight-b value-b)))

(defn total-weight
  "The total sample weight."
  [weight-a weight-b]
  (+ weight-a weight-b))

(defn importance-estimate
  "The importance estimate: weighted sum normalized by the total weight."
  [weight-a value-a weight-b value-b]
  (/ (weighted-sum weight-a value-a weight-b value-b)
     (total-weight weight-a weight-b)))
