(ns rainbow.algorithms.reference.momentum
  "Executable exact-rational Polyak momentum descent with pair state. The state is
  a [position velocity] vector. Each step accumulates velocity
  `v' = beta * v - rate * gradient(position)` (the momentum term `beta * v` is
  what plain gradient descent lacks) and moves `x' = x + v'`. Matches the proved
  Rainbow definitions.")

(defn velocity-update
  "The accumulated velocity: momentum carry minus the rate-scaled gradient."
  [beta rate gradient x v]
  (- (* beta v) (* rate (gradient x))))

(defn step
  "One momentum step over the [position velocity] state."
  [beta rate gradient [x v]]
  (let [v' (velocity-update beta rate gradient x v)]
    [(+ x v') v']))

(defn run
  "Iterate the momentum step n times from the initial [position velocity] state."
  [beta rate gradient n initial]
  (nth (iterate (partial step beta rate gradient) initial) n))
