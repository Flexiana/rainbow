(ns rainbow.algorithms.reference.gradient-descent
  "Executable exact-rational bounded gradient descent. Each step subtracts the
  rate-scaled gradient from the current point; with exact rationals the
  trajectory can pass through zero into negative values, matching the proved
  signed-rational Rainbow definition. The gradient and rate are pluggable.")

(defn descent-step
  "One exact gradient-descent update: point - rate * (gradient point)."
  [rate gradient point]
  (- point (* rate (gradient point))))

(defn descent-iterate
  "Run a bounded number of exact gradient-descent steps from initial."
  [rate gradient steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Descent steps must be a natural integer" {:steps steps})))
  (nth (iterate #(descent-step rate gradient %) initial) steps))

(defn trajectory
  "The first steps+1 exact iterates as a vector."
  [rate gradient initial steps]
  (mapv #(descent-iterate rate gradient % initial) (range (inc steps))))
