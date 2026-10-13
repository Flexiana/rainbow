(ns rainbow.algorithms.reference.pattern-search
  "Executable exact-rational generalized pattern search. The poll picks the
  candidate with the smaller objective value (argmin of two), and the move is
  accepted when the polled best improves on the current objective -- a
  derivative-free step using only objective comparisons. Matches the proved
  Rainbow definitions.")

(defn poll-better
  "Pick the point with the smaller objective value (argmin of two candidates)."
  [value-a value-b point-a point-b]
  (if (<= value-a value-b) point-a point-b))

(defn poll-improves?
  "The polled best improves the current when its objective is at most the
  current objective."
  [best-value current-value]
  (<= best-value current-value))

(defn pattern-move
  "Move to the polled best if it improves, otherwise keep the current point."
  [best-value current-value best-point current-point]
  (if (poll-improves? best-value current-value) best-point current-point))

(defn step
  "One pattern search step: poll two candidates by objective, move if improving."
  [objective current-point forward-point backward-point]
  (let [vf (objective forward-point)
        vb (objective backward-point)
        vc (objective current-point)
        best-value (min vf vb)
        best-point (poll-better vf vb forward-point backward-point)]
    (pattern-move best-value vc best-point current-point)))
