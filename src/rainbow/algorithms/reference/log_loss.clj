(ns rainbow.algorithms.reference.log-loss
  "Executable cross-entropy / log loss, matching the proved Rainbow ordering.")

(defn lower-loss? [p-confident p-unsure] (<= p-unsure p-confident))

(defn log-loss
  "Per-example cross-entropy loss for the true-class probability p."
  [p]
  (- (Math/log p)))

(defn binary-cross-entropy
  "Mean binary cross-entropy over (y, p) pairs (y in {0,1}, p predicted P(y=1))."
  [examples]
  (/ (reduce + (map (fn [[y p]]
                      (- (+ (* y (Math/log p))
                            (* (- 1 y) (Math/log (- 1 p))))))
                    examples))
     (count examples)))
