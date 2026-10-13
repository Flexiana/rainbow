(ns rainbow.algorithms.reference.perceptron
  "Executable perceptron, matching the proved Rainbow firing rule.")

(defn fires? [activation threshold] (<= threshold activation))

(defn predict
  "Perceptron prediction (1 or 0) for weights, bias, and input x (dot product)."
  [weights bias x]
  (let [activation (+ bias (reduce + (map * weights x)))]
    (if (fires? activation 0) 1 0)))

(defn train
  "Mistake-driven perceptron learning over labeled examples [x y] for epochs.
  Returns [weights bias]."
  [n-features examples epochs]
  (loop [w (vec (repeat n-features 0)), b 0, e 0]
    (if (= e epochs)
      [w b]
      (let [[w' b'] (reduce (fn [[w b] [x y]]
                              (let [yhat (predict w b x)
                                    err (- y yhat)]
                                [(mapv (fn [wi xi] (+ wi (* err xi))) w x)
                                 (+ b err)]))
                            [w b] examples)]
        (recur w' b' (inc e))))))
