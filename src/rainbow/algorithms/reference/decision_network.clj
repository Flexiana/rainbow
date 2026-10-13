(ns rainbow.algorithms.reference.decision-network
  "Executable exact-rational decision network evaluation: the expected utility is
  the probability-weighted sum of the utilities over the outcomes. Matches the
  proved Rainbow definitions.")

(defn network-value
  "Evaluate the decision network: the expected utility under the chance masses."
  [outcomes probability utility]
  (reduce + 0 (map (fn [o] (* (probability o) (utility o))) outcomes)))
