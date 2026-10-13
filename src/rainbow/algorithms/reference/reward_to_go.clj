(ns rainbow.algorithms.reference.reward-to-go
  "Executable exact Reward-to-Go (AHoF D47). The total matches the proved Rainbow
  definition (fold-sum of the reward suffix); `to-go-sequence` realizes the
  one-backward-pass computation of the reward-to-go value at every step, which is
  what policy-gradient estimators weight each action by.")

(defn reward-to-go
  "Sum of the reward suffix (future rewards from the current step onward)."
  [rewards]
  (reduce + 0 rewards))

(defn to-go-sequence
  "Reward-to-go value at each step, computed in a single backward pass:
  [r0 r1 r2] -> [r0+r1+r2, r1+r2, r2]."
  [rewards]
  (vec (reverse (reductions + (reverse rewards)))))
