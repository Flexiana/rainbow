(ns rainbow.algorithms.reference.gae
  "Executable Generalized Advantage Estimation, matching the proved Rainbow
  definition.")

(defn gae2
  "Two-step GAE advantage: d0 + w*d1, w = gamma*lambda."
  [d0 d1 w]
  (+ d0 (* w d1)))

(defn gae
  "General GAE advantage over a vector of TD errors with weight w = gamma*lambda."
  [td-errors w]
  (reduce (fn [acc d] (+ (* acc w) d)) 0 (reverse td-errors)))
