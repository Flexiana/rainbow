(ns rainbow.algorithms.reference.softmax
  "Executable softmax, matching the proved Rainbow normalization.")

(defn softmax-share [exp-score total-exp] (/ exp-score total-exp))

(defn softmax
  "Softmax of a score vector: exp(x_i - max) / sum. Uses floats for exp."
  [scores]
  (let [m (apply max scores)
        exps (map #(Math/exp (- % m)) scores)
        total (reduce + exps)]
    (mapv #(softmax-share % total) exps)))
