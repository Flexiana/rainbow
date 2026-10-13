(ns rainbow.algorithms.reference.nearest-neighbor
  "Executable exact-rational nearest-neighbor value function approximation: the
  approximated value at a query is the stored value of the nearer of two data
  points, selected by comparing their distances to the query. Matches the proved
  Rainbow definitions.")

(defn nearest-value
  "Return the value of the nearer point (the smaller distance)."
  [distance-a value-a distance-b value-b]
  (if (<= distance-a distance-b) value-a value-b))
