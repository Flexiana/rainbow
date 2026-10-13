(ns rainbow.algorithms.reference.penalty
  "Executable penalty-method objective, matching the proved Rainbow definition.")

(defn penalized
  "Penalized objective: f + mu*violation."
  [f mu violation]
  (+ f (* mu violation)))

(defn penalty-path
  "Penalized objective along an increasing mu schedule at a fixed point."
  [f violation mus]
  (map #(penalized f % violation) mus))
