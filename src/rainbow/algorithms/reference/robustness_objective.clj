(ns rainbow.algorithms.reference.robustness-objective
  "Executable exact-rational robustness-based falsification objective. The
  objective negates the STL robustness, so a satisfying trajectory (positive
  robustness) has a negative objective and a violating trajectory (negative
  robustness) has a positive one -- maximizing the objective drives falsification.
  Matches the proved Rainbow definitions.")

(defn falsification-objective
  "Negate the robustness: satisfying trajectories score negative, violating
  trajectories score positive."
  [robustness]
  (- robustness))
