(ns rainbow.algorithms.reference.natural-gradient
  "Executable exact-rational natural-gradient update (AHoF D50). The update
  matches the proved Rainbow definition; `precondition` applies a supplied
  inverse-Fisher matrix to the ordinary gradient to form the natural gradient."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn update-step
  "theta' = theta + rate * natural."
  [theta rate natural]
  (vector/add theta (vector/scale rate natural)))

(defn precondition
  "Natural gradient = F^{-1} * grad. `apply-inverse-fisher` is a supplied linear
  map (rows as vectors) applied to the ordinary gradient."
  [apply-inverse-fisher grad]
  (apply-inverse-fisher grad))
