(ns rainbow.algorithms.reference.dual-ascent
  "Executable exact-rational Dual Ascent (AHoF O52). The ascent step matches the
  proved Rainbow definition; the outer loop iterates the multiplier update over a
  supplied primal solver (x-star) and residual map (A*x - b), both pluggable
  functions over exact rationals."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn ascent-step
  "lambda' = lambda + rate * residual."
  [multiplier residual rate]
  (vector/add multiplier (vector/scale rate residual)))

(defn iterate-dual
  "Run `steps` dual-ascent updates. `residual-fn` maps the current multiplier to
  the primal constraint residual r = A*x*(lambda) - b (the dual gradient); the
  primal minimization is folded inside `residual-fn`."
  [residual-fn multiplier rate steps]
  (nth (iterate (fn [current]
                  (ascent-step current (residual-fn current) rate))
                multiplier)
       steps))
