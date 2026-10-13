(ns rainbow.algorithms.reference.differential-evolution
  "Executable exact-rational Differential Evolution (AHoF O44). The differential
  mutation matches the proved Rainbow definitions; binomial crossover and greedy
  selection (the population dynamics the proved core leaves as executable
  concerns) are included here over exact rational fitness values."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn scaled-difference
  "donor = F * (b - c)."
  [f b c]
  (vector/scale f (vector/subtract b c)))

(defn differential-mutation
  "DE/rand/1 mutant = base + F * (b - c)."
  [base f b c]
  (vector/add base (scaled-difference f b c)))

(defn binomial-crossover
  "Take component i from the mutant where the mask is truthy, else from the
  target. Models DE's per-dimension crossover with an explicit mask."
  [target mutant mask]
  (mapv (fn [t m keep?] (if keep? m t)) target mutant mask))

(defn select
  "Greedy selection: keep whichever of target/trial has the lower objective
  (target wins ties, matching the usual DE convention)."
  [objective target trial]
  (if (< (objective trial) (objective target)) trial target))
