(ns rainbow.algorithms.reference.firefly
  "Executable exact-rational Firefly Algorithm (AHoF O46). The attraction move
  matches the proved Rainbow definition; brightness comparison (the selection of
  which firefly is brighter) is included here over exact rational objectives."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn attraction-step
  "x' = x + beta * (bright - x)."
  [position bright beta]
  (vector/add position (vector/scale beta (vector/subtract bright position))))

(defn brighter?
  "A firefly is brighter when its objective is lower (minimization convention)."
  [objective a b]
  (< (objective a) (objective b)))

(defn move-toward-brighter
  "Move `position` toward `other` only when `other` is brighter, else stay."
  [objective position other beta]
  (if (brighter? objective other position)
    (attraction-step position other beta)
    position))
