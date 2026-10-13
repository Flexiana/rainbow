(ns rainbow.algorithms.reference.ista
  "Executable ISTA soft-thresholding, matching the proved Rainbow definition.")

(defn shrinks-to-zero?
  "True iff a coefficient magnitude is within the threshold (zeroed)."
  [m lambda]
  (<= m lambda))

(defn soft-threshold
  "Soft-thresholding (shrinkage) operator: sign(x)*max(|x|-lambda, 0)."
  [x lambda]
  (let [m (abs x)]
    (if (shrinks-to-zero? m lambda)
      0
      (* (if (neg? x) -1 1) (- m lambda)))))
