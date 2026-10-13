(ns rainbow.algorithms.reference.box-projection
  "Executable exact-rational box projection (projected gradient descent step).
  The clamp matches the proved Rainbow definition; `projected-step` performs an
  unconstrained update and projects the result back onto the feasible box.")

(defn clamp
  "Project x onto the box [lo, hi]: max(lo, min(x, hi))."
  [lo hi x]
  (max lo (min x hi)))

(defn feasible?
  "Whether x already lies in the box [lo, hi]."
  [lo hi x]
  (and (<= lo x) (<= x hi)))

(defn projected-step
  "One projected-gradient step on a box [lo, hi]: descend by rate*gradient from
  x, then project back onto the box."
  [lo hi x gradient rate]
  (clamp lo hi (- x (* rate gradient))))
