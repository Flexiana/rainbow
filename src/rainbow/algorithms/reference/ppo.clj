(ns rainbow.algorithms.reference.ppo
  "Executable PPO clip (clamp the probability ratio into the trust band),
  matching the proved Rainbow definition.")

(defn ppo-clip
  "Clamp ratio r into [lo, hi] = max(lo, min(r, hi))."
  [r lo hi]
  (max lo (min r hi)))

(defn clipped-surrogate
  "PPO clipped surrogate term: min(r*A, clip(r,1-eps,1+eps)*A) for advantage A."
  [r advantage epsilon]
  (min (* r advantage)
       (* (ppo-clip r (- 1 epsilon) (+ 1 epsilon)) advantage)))
