(ns rainbow.algorithms.reference.linear-regression-vf
  "Executable exact-rational Linear Regression VF (AHoF D29). The two-feature
  prediction matches the proved Rainbow definition; `predict` is the dot product
  of weights and features.")

(defn predict-two [w1 f1 w2 f2] (+ (* w1 f1) (* w2 f2)))

(defn predict
  "Linear VF prediction: dot product of weights and feature values."
  [weights features]
  (reduce + 0 (map * weights features)))
