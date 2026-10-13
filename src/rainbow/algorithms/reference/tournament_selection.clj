(ns rainbow.algorithms.reference.tournament-selection
  "Executable exact-rational tournament selection (AHoF O43 GA operator). The
  pairwise max and the tournament winner match the proved Rainbow definitions;
  `tournament` draws a k-sized tournament from a population by index and returns
  the fittest entrant, the selection primitive a genetic algorithm repeats to
  form the mating pool.")

(defn nnrat-max
  "The larger of two fitnesses."
  [l r]
  (if (<= l r) r l))

(defn winner
  "The fittest entrant of a tournament (max-fold of the fitnesses)."
  [fitnesses]
  (reduce nnrat-max 0 fitnesses))

(defn tournament
  "Select the fittest of the entrants at the given indices into `population`
  (a vector of fitnesses)."
  [population indices]
  (winner (map population indices)))
