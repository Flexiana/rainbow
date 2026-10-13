(ns rainbow.algorithms.reference.coordinate-search
  "Executable exact-rational cyclic coordinate search over a [x y] pair state. A
  cycle descends the first coordinate, then descends the second coordinate of the
  already-updated state -- optimizing along each coordinate in turn (reduce over
  dimensions). Matches the proved Rainbow definitions.")

(defn update-first
  "Descend the first coordinate by its partial gradient."
  [rate gradient [x y :as s]]
  [(- x (* rate (gradient s))) y])

(defn update-second
  "Descend the second coordinate by its partial gradient."
  [rate gradient [x y :as s]]
  [x (- y (* rate (gradient s)))])

(defn cycle-once
  "One coordinate cycle: descend the first coordinate, then the second of the
  updated state."
  [rate gradient-first gradient-second s]
  (update-second rate gradient-second (update-first rate gradient-first s)))

(defn run
  "Iterate the coordinate cycle n times from the initial [x y] state."
  [rate gradient-first gradient-second n initial]
  (nth (iterate (partial cycle-once rate gradient-first gradient-second)
                initial)
       n))
