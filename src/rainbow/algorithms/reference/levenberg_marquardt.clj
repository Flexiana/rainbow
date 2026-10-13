(ns rainbow.algorithms.reference.levenberg-marquardt
  "Executable exact-rational Levenberg-Marquardt: the descent step scaled by the
  reciprocal of the damped Hessian. `step(x) = x - (1 / (hessian(x) + lambda)) *
  gradient(x)`. Lambda = 0 recovers Newton; large lambda gives small gradient
  steps. Matches the proved Rainbow definitions.")

(defn rate
  "The damped step size: the reciprocal of the Hessian plus the damping lambda."
  [hessian lambda point]
  (/ 1 (+ (hessian point) lambda)))

(defn step
  "One Levenberg-Marquardt step: descend scaled by the inverse damped Hessian."
  [hessian lambda gradient point]
  (- point (* (rate hessian lambda point) (gradient point))))

(defn run
  "Iterate the Levenberg-Marquardt step n times from the initial point."
  [hessian lambda gradient n initial]
  (nth (iterate (partial step hessian lambda gradient) initial) n))
