(ns rainbow.algorithms.reference.cmaes
  "Executable exact-rational CMA-ES mean recombination (AHoF O42). The two-elite
  recombination matches the proved Rainbow definition; `recombine` generalizes to
  the weighted mean of any number of ranked elite samples."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn recombine-two
  "w1*x1 + w2*x2."
  [w1 x1 w2 x2]
  (vector/add (vector/scale w1 x1) (vector/scale w2 x2)))

(defn recombine
  "CMA-ES mean: the weighted recombination of ranked elite samples."
  [weights elite]
  (reduce vector/add
          (map (fn [w x] (vector/scale w x)) weights elite)))
