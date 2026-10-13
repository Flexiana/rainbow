(ns rainbow.algorithms.reference.value-of-information
  "Executable exact-rational value of information: the signed difference between
  informed and uninformed expected utility. Information never hurts, so the value
  of information is nonnegative whenever the informed expected utility dominates.
  This matches the proved Rainbow signed-rational definition.")

(defn value-of-information
  "The exact value of information EU(with info) - EU(without info)."
  [eu-with-info eu-without-info]
  (- eu-with-info eu-without-info))

(defn information-never-hurts?
  "True when the informed expected utility is at least the uninformed one."
  [eu-with-info eu-without-info]
  (>= eu-with-info eu-without-info))
