(ns rainbow.algorithms.reference.odd-monitor
  "Executable exact-rational ODD monitor: an operating point lies inside the 2-D
  operating envelope [lo1,hi1] x [lo2,hi2] exactly when both coordinates are within
  their bounds. Matches the proved Rainbow definition.")

(defn in-odd?
  "True when (x1, x2) lies inside the box [lo1,hi1] x [lo2,hi2]."
  [lo1 hi1 x1 lo2 hi2 x2]
  (and (<= lo1 x1) (<= x1 hi1) (<= lo2 x2) (<= x2 hi2)))
