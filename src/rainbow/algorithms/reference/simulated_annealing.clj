(ns rainbow.algorithms.reference.simulated-annealing
  "Executable exact-rational Simulated Annealing (AHoF O40). The geometric
  cooling schedule and greedy-limit acceptance match the proved Rainbow
  definitions; the full Metropolis criterion (which accepts an uphill move by an
  exp(-delta/T) probability) is included here as the executable stochastic
  concern, parameterized by an explicit acceptance draw so it stays exact.")

(defn cool
  "Geometric temperature schedule: T' = alpha * T."
  [alpha temperature]
  (* alpha temperature))

(defn accept-better?
  "Greedy-limit acceptance: accept a candidate that does not worsen the cost."
  [candidate-cost current-cost]
  (<= candidate-cost current-cost))

(defn metropolis-accept?
  "Full acceptance with an explicit draw in [0,1): a non-worsening candidate is
  always accepted; an uphill candidate is accepted when the draw is below the
  acceptance ratio threshold (supplied exactly rather than sampled)."
  [candidate-cost current-cost threshold draw]
  (or (accept-better? candidate-cost current-cost)
      (< draw threshold)))

(defn step
  "One greedy annealing step over exact rational costs: keep whichever of
  current/candidate has the lower cost, and cool the temperature."
  [cost current candidate temperature alpha]
  {:state (if (accept-better? (cost candidate) (cost current)) candidate current)
   :temperature (cool alpha temperature)})
