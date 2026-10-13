(ns rainbow.algorithms.reference.general-descent
  "Executable exact-rational general descent skeleton. A step delegates to three
  pluggable functions -- a direction, a step size, and an update rule -- and
  composes them: `update(point, step-size(point), direction(point))`. Gradient
  descent, momentum, and Newton's method are all this skeleton with particular
  plug-ins. Matches the proved Rainbow definitions.")

(defn step
  "One general descent step, delegating to the three plug-in functions."
  [direction step-size update point]
  (update point (step-size point) (direction point)))

(defn run
  "Iterate the general descent step n times from the initial point."
  [direction step-size update n initial]
  (nth (iterate (partial step direction step-size update) initial) n))
