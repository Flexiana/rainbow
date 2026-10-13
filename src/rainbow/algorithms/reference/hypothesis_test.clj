(ns rainbow.algorithms.reference.hypothesis-test
  "Executable hypothesis test decision, matching the proved Rainbow rule.")

(defn reject-null? [statistic critical] (<= critical statistic))

(defn z-test
  "Two-sided z-test: |sample-mean - mu0| / (sigma/sqrt n) vs critical value.
  Returns :reject or :fail-to-reject. Uses rational inputs for exactness where
  possible; sqrt is a float."
  [sample-mean mu0 sigma n critical]
  (let [z (/ (abs (- sample-mean mu0)) (/ sigma (Math/sqrt n)))]
    (if (reject-null? z critical) :reject :fail-to-reject)))
