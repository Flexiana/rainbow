(ns rainbow.algorithms.reference.neural-vf
  "Executable exact-rational Neural Network VF (AHoF D30). The neuron
  pre-activation matches the proved Rainbow definition; `layer` applies a full
  linear layer with a ReLU activation.")

(defn neuron [w1 x1 w2 x2 b] (+ (* w1 x1) (* w2 x2) b))

(defn relu [x] (max 0 x))

(defn layer
  "Apply a linear layer (weight matrix `W` as rows, bias vector `b`) to input `x`
  with ReLU activation."
  [W b x]
  (mapv (fn [row bias] (relu (+ bias (reduce + 0 (map * row x))))) W b))
