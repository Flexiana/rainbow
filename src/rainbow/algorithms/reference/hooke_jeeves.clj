(ns rainbow.algorithms.reference.hooke-jeeves
  "Executable exact-rational Hooke-Jeeves pattern search (AHoF O34). The
  exploratory probe and pattern (acceleration) move match the proved Rainbow
  definitions; the acceptance test (keep a probe only when it improves) is the
  executable direct-search concern."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn probe
  "Exploratory move: step away from the base."
  [base step]
  (vector/add base step))

(defn pattern-move
  "Pattern (acceleration) move: extrapolate past the improved point."
  [base improved]
  (vector/add improved (vector/subtract improved base)))

(defn accept
  "Keep the probe only when it strictly improves the objective, else the base."
  [objective base probed]
  (if (< (objective probed) (objective base)) probed base))
