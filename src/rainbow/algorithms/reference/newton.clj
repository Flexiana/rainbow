(ns rainbow.algorithms.reference.newton
  "Executable exact-rational Newton's method: the descent step scaled by the
  reciprocal of the Hessian. `step(x) = x - (1 / hessian(x)) * gradient(x)`. On a
  quadratic the Hessian is constant and Newton reaches the minimum in one step.
  Matches the proved Rainbow definitions.")

(defn rate
  "The Newton step size: the reciprocal of the Hessian at the point."
  [hessian point]
  (/ 1 (hessian point)))

(defn step
  "One Newton step: descend scaled by the inverse Hessian."
  [hessian gradient point]
  (- point (* (rate hessian point) (gradient point))))

(defn run
  "Iterate the Newton step n times from the initial point."
  [hessian gradient n initial]
  (nth (iterate (partial step hessian gradient) initial) n))
