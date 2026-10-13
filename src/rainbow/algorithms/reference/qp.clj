(ns rainbow.algorithms.reference.qp
  "Executable exact-rational Quadratic Programming (AHoF O56). The scalar
  objective matches the proved Rainbow definition; `minimize-1d` returns the
  unconstrained minimizer of q x^2 + c x (q > 0), which solves the KKT
  stationarity 2 q x + c = 0.")

(defn objective
  "q*x^2 + c*x."
  [q x c]
  (+ (* q x x) (* c x)))

(defn minimize-1d
  "Unconstrained minimizer of q x^2 + c x for q > 0: x* = -c / (2 q)."
  [q c]
  (/ (- c) (* 2 q)))
