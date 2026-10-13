(ns rainbow.algorithms.reference.baseline-subtraction
  "Executable exact-rational baseline subtraction (AHoF D48). The baselined
  contribution matches the proved Rainbow definition; `baselined-gradient`
  applies a baseline to a batch of (return, score) trajectories.")

(defn contribution
  "advantage * score."
  [advantage score]
  (* advantage score))

(defn baselined-gradient
  "Variance-reduced policy-gradient estimate: mean over trajectories of
  (return - baseline) * score."
  [baseline trajectories]
  (if (empty? trajectories)
    0
    (/ (reduce + 0 (map (fn [[r s]] (contribution (- r baseline) s)) trajectories))
       (count trajectories))))
