(ns rainbow.algorithms.reference.augmented-lagrangian
  "Executable exact-rational Augmented Lagrangian multiplier update (AHoF O49).
  Matches the proved Rainbow definition; the inner penalized minimization and the
  augmented-Lagrangian value are the executable optimizer's concern."
  (:refer-clojure :exclude [max]))

(defn update-multiplier
  "multiplier' = multiplier + rho * constraint."
  [multiplier rho constraint]
  (+ multiplier (* rho constraint)))

(defn augmented-value
  "The augmented Lagrangian value: f + lambda*c + (rho/2)*c^2."
  [objective multiplier rho constraint]
  (+ objective (* multiplier constraint) (* (/ rho 2) constraint constraint)))
