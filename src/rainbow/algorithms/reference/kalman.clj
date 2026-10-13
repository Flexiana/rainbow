(ns rainbow.algorithms.reference.kalman
  "Executable scalar Kalman filter update, matching the proved Rainbow
  definitions.")

(defn kalman-gain [p r] (/ p (+ p r)))

(defn kalman-posterior [p r] (/ (* p r) (+ p r)))

(defn update-mean
  "Posterior mean: x + K*(z - x) for measurement z."
  [x p z r]
  (+ x (* (kalman-gain p r) (- z x))))
