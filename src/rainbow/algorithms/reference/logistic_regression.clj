(ns rainbow.algorithms.reference.logistic-regression
  "Executable logistic regression, matching the proved Rainbow decision.")

(defn sigmoid [z] (/ 1.0 (+ 1.0 (Math/exp (- z)))))

(defn classify-positive? [probability threshold] (<= threshold probability))

(defn predict-proba [weights bias x]
  (sigmoid (+ bias (reduce + (map * weights x)))))

(defn classify [weights bias x]
  (if (classify-positive? (predict-proba weights bias x) 0.5) 1 0))

(defn train
  "Gradient ascent on log-likelihood. examples are [x y]."
  [n-features examples rate epochs]
  (loop [w (vec (repeat n-features 0.0)), b 0.0, e 0]
    (if (= e epochs)
      [w b]
      (let [[w' b'] (reduce (fn [[w b] [x y]]
                              (let [err (- y (predict-proba w b x))]
                                [(mapv (fn [wi xi] (+ wi (* rate err xi))) w x)
                                 (+ b (* rate err))]))
                            [w b] examples)]
        (recur w' b' (inc e))))))
