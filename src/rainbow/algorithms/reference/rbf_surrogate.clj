(ns rainbow.algorithms.reference.rbf-surrogate
  "Executable exact-rational RBF surrogate (AHoF O61). The two-center prediction
  matches the proved Rainbow definition; `predict` generalizes to any number of
  centers as the weighted sum of supplied basis evaluations.")

(defn predict-two
  "w1*phi1 + w2*phi2."
  [w1 phi1 w2 phi2]
  (+ (* w1 phi1) (* w2 phi2)))

(defn predict
  "RBF prediction: sum of weights * basis-function evaluations."
  [weights basis-values]
  (reduce + 0 (map * weights basis-values)))
