(ns rainbow.algorithms.reference.hmc
  "Executable exact-rational HMC leapfrog (AHoF V24). The position drift matches
  the proved Rainbow definition; `leapfrog` runs one full leapfrog step
  (momentum half-kick, position drift, momentum half-kick)."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn drift
  "Leapfrog position update: q + step * momentum."
  [q step momentum]
  (vector/add q (vector/scale step momentum)))

(defn kick
  "Leapfrog momentum half-kick: p - (step/2) * gradient-U."
  [p step grad-u]
  (vector/subtract p (vector/scale (/ step 2) grad-u)))

(defn leapfrog
  "One leapfrog step of Hamiltonian dynamics from (q, p) with potential gradient
  `grad-u` (a function of position) and step size `step`."
  [q p grad-u step]
  (let [p-half (kick p step (grad-u q))
        q-next (drift q step p-half)
        p-next (kick p-half step (grad-u q-next))]
    [q-next p-next]))
