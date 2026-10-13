(ns rainbow.algorithms.reference.roulette-selection
  "Executable fitness-proportionate (roulette-wheel) selection. The wheel is the
  cumulative fitness (prefix-sum scan); a spin selects the first individual whose
  cumulative fitness reaches it."
  (:require [rainbow.algorithms.reference.prefix-sum :as prefix-sum]))

(defn wheel
  "Cumulative-fitness wheel for a fitness vector."
  [fitnesses]
  (prefix-sum/cumulative-sum fitnesses))

(defn select-index
  "Index of the individual the spin s lands on, given fitnesses."
  [fitnesses s]
  (let [w (wheel fitnesses)]
    (or (first (keep-indexed (fn [i c] (when (<= s c) i)) w))
        (dec (count fitnesses)))))
