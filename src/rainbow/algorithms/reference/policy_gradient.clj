(ns rainbow.algorithms.reference.policy-gradient
  "Executable exact-rational policy-gradient ascent update (AHoF D49). The update
  matches the proved Rainbow definition; `ascend` iterates it over a supplied
  gradient estimator."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn update-step
  "theta' = theta + rate * gradient."
  [theta rate gradient]
  (vector/add theta (vector/scale rate gradient)))

(defn ascend
  "Run `steps` policy-gradient ascent updates. `gradient-of` maps the current
  parameters to a policy-gradient estimate."
  [gradient-of theta rate steps]
  (nth (iterate (fn [current]
                  (update-step current rate (gradient-of current)))
                theta)
       steps))
