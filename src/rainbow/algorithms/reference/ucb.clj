(ns rainbow.algorithms.reference.ucb
  "Executable exact-rational UCB acquisition (AHoF O64). The acquisition matches
  the proved Rainbow definition; `select` picks the candidate maximizing the UCB
  over supplied (mean, uncertainty) surrogate predictions.")

(defn acquisition
  "ucb = mean + weight * uncertainty."
  [mean weight uncertainty]
  (+ mean (* weight uncertainty)))

(defn select
  "Choose the candidate with the highest UCB. `predict` maps a candidate to its
  [mean uncertainty] surrogate prediction; `weight` is the exploration weight."
  [predict weight candidates]
  (apply max-key
         (fn [c] (let [[mean uncertainty] (predict c)]
                   (acquisition mean weight uncertainty)))
         candidates))
