(ns rainbow.algorithms.reference.frank-wolfe
  "Executable Frank-Wolfe convex-combination step, matching the proved Rainbow
  definition.")

(defn fw-step
  "Convex-combination update w0*x + w1*s (w0 + w1 = 1)."
  [x s w0 w1]
  (+ (* w0 x) (* w1 s)))

(defn fw-step-gamma
  "Frank-Wolfe update with step gamma toward vertex s: (1-gamma)x + gamma*s."
  [x s gamma]
  (fw-step x s (- 1 gamma) gamma))
