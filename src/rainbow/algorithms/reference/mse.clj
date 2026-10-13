(ns rainbow.algorithms.reference.mse
  "Executable mean squared error, matching the proved Rainbow definitions.")

(defn squared-error [e] (* e e))

(defn mse
  "Mean squared error of residuals (predictions minus targets)."
  [residuals]
  (/ (reduce + (map squared-error residuals)) (count residuals)))

(defn mse-predictions
  "MSE between predictions and targets."
  [predictions targets]
  (mse (map - predictions targets)))
