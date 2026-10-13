(ns rainbow.algorithms.reference.powell
  "Executable exact-rational Powell's Method direction generation (AHoF O33).
  The conjugate net-direction matches the proved Rainbow definition; the
  direction-set rotation (drop the oldest direction, append the new one) is the
  executable bookkeeping."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn net-direction
  "The new conjugate direction: net displacement over a cycle."
  [start end]
  (vector/subtract end start))

(defn rotate-directions
  "Replace the direction set by dropping the oldest and appending the new one."
  [directions new-direction]
  (conj (vec (rest directions)) new-direction))
