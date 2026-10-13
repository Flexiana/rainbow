(ns rainbow.algorithms.reference.conjugate-gradient
  "Executable exact-rational conjugate gradient with pair state. The state is a
  [position direction] vector. Each step forms a new direction from the current
  negative gradient plus beta times the remembered previous direction, then moves
  the position by alpha along the new direction. Matches the proved Rainbow
  definitions.")

(defn conjugate-direction
  "New search direction: negative gradient plus beta times the remembered one."
  [beta gradient x d]
  (+ (- (gradient x)) (* beta d)))

(defn step
  "One conjugate gradient step over the [position direction] state."
  [alpha beta gradient [x d]]
  (let [d' (conjugate-direction beta gradient x d)]
    [(+ x (* alpha d')) d']))

(defn run
  "Iterate the conjugate gradient step n times from the initial state."
  [alpha beta gradient n initial]
  (nth (iterate (partial step alpha beta gradient) initial) n))
