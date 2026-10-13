(ns rainbow.algorithms.reference.metropolis
  "Executable Metropolis-Hastings / Simulated Annealing acceptance (AHoF V22).
  The deterministic downhill test matches the proved Rainbow definition; the full
  rule adds the stochastic Boltzmann acceptance of uphill proposals, with the
  temperature and RNG supplied by the caller.")

(defn accepts-downhill?
  "A proposal is deterministically accepted when its energy does not exceed the
  current energy."
  [proposed current]
  (<= proposed current))

(defn accept?
  "Full Metropolis rule: accept downhill always; accept uphill with probability
  exp(-(proposed - current)/temperature), sampled via `uniform` in [0,1)."
  [proposed current temperature uniform]
  (or (accepts-downhill? proposed current)
      (< uniform (Math/exp (/ (- (- proposed current)) temperature)))))
