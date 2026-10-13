(ns rainbow.algorithms.reference.noisy-descent
  "Executable exact-rational Noisy Descent (AHoF O38). The additive-noise wrap
  matches the proved Rainbow definition; the base descent step and the noise
  draw are the wrapped optimizer's and sampler's concern."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn wrap
  "Perturb a base step result with additive noise."
  [step noise]
  (vector/add step noise))

(defn noisy-descent-step
  "A full noisy gradient step: move against the scaled gradient, then perturb.
  x' = (x - rate*gradient) + noise."
  [position gradient rate noise]
  (wrap (vector/subtract position (vector/scale rate gradient)) noise))
