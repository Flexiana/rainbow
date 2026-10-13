(ns rainbow.algorithms.reference.nesterov
  "Executable exact-rational Nesterov accelerated momentum with pair state. Unlike
  Polyak momentum, the gradient is evaluated at the look-ahead point `x + beta*v`
  rather than at `x`: `v' = beta*v - rate*gradient(x + beta*v)`, `x' = x + v'`.
  When the gradient depends on position the look-ahead changes the trajectory.
  Matches the proved Rainbow definitions.")

(defn lookahead
  "The look-ahead point where Nesterov evaluates the gradient."
  [beta x v]
  (+ x (* beta v)))

(defn velocity-update
  "Velocity from the momentum carry minus the look-ahead-scaled gradient."
  [beta rate gradient x v]
  (- (* beta v) (* rate (gradient (lookahead beta x v)))))

(defn step
  "One Nesterov step over the [position velocity] state."
  [beta rate gradient [x v]]
  (let [v' (velocity-update beta rate gradient x v)]
    [(+ x v') v']))

(defn run
  "Iterate the Nesterov step n times from the initial [position velocity] state."
  [beta rate gradient n initial]
  (nth (iterate (partial step beta rate gradient) initial) n))
