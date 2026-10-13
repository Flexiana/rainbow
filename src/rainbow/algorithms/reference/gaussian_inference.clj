(ns rainbow.algorithms.reference.gaussian-inference
  "Executable exact-rational Gaussian conjugate inference (AHoF D9). The precision
  update matches the proved Rainbow definition; `posterior` returns the full
  precision-weighted conjugate posterior (mean and precision).")

(defn posterior-precision
  "Conjugate precision update: prior + likelihood."
  [prior likelihood]
  (+ prior likelihood))

(defn posterior
  "Gaussian conjugate posterior from prior (mean, precision) and observation
  (value, precision): precision adds; the mean is the precision-weighted average."
  [prior-mean prior-prec obs-value obs-prec]
  (let [prec (posterior-precision prior-prec obs-prec)]
    {:precision prec
     :mean (/ (+ (* prior-prec prior-mean) (* obs-prec obs-value)) prec)}))
