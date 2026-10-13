(ns rainbow.algorithms.reference.reinforce
  "Executable exact-rational REINFORCE estimator (AHoF D46). The two-trajectory
  estimate matches the proved Rainbow definition; `gradient` is the full batch
  mean of return-weighted scores.")

(defn estimate-two
  "r1*s1 + r2*s2."
  [r1 s1 r2 s2]
  (+ (* r1 s1) (* r2 s2)))

(defn gradient
  "REINFORCE policy-gradient estimate: mean over trajectories of return*score.
  `trajectories` is a seq of [return score]."
  [trajectories]
  (if (empty? trajectories)
    0
    (/ (reduce + 0 (map (fn [[r s]] (* r s)) trajectories))
       (count trajectories))))
