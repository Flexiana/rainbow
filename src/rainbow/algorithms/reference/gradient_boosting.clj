(ns rainbow.algorithms.reference.gradient-boosting
  "Executable gradient boosting, matching the proved Rainbow update.")

(defn boost-update [current learning-rate weak]
  (+ current (* learning-rate weak)))

(defn boost
  "Run m rounds of boosting from an initial prediction, with a sequence of weak
  predictions and a fixed learning rate."
  [initial learning-rate weak-predictions]
  (reduce (fn [f w] (boost-update f learning-rate w)) initial weak-predictions))
