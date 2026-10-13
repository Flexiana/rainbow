(ns rainbow.algorithms.reference.admm
  "Executable exact-rational ADMM scaled dual update (AHoF O51). The dual update
  matches the proved Rainbow definition; the x- and z-subproblem solvers are
  pluggable functions over exact rationals supplied to the iteration."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn dual-update
  "u' = u + (x - z)."
  [dual x z]
  (vector/add dual (vector/subtract x z)))

(defn iterate-admm
  "Run `steps` ADMM rounds. `x-update` maps (z, dual) to the next x; `z-update`
  maps (x, dual) to the next z; the scaled dual accumulates the primal residual."
  [x-update z-update dual x z steps]
  (nth (iterate (fn [[dual x z]]
                  (let [x* (x-update z dual)
                        z* (z-update x* dual)]
                    [(dual-update dual x* z*) x* z*]))
                [dual x z])
       steps))
