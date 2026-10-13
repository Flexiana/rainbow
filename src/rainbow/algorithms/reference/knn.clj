(ns rainbow.algorithms.reference.knn
  "Executable K-nearest-neighbors classification, matching the proved Rainbow
  prediction."
  (:require [rainbow.algorithms.reference.argmax-index :as argmax-index]))

(defn knn-predict
  "Predicted class = argmax of the per-class vote counts."
  [votes]
  (argmax-index/argmax-index votes))

(defn classify
  "K-NN over labeled examples [features label] with an integer number of classes.
  dist is a distance function."
  [k n-classes examples dist query]
  (let [nearest (take k (sort-by #(dist query (first %)) examples))
        votes (reduce (fn [v [_ y]] (update v y inc))
                      (vec (repeat n-classes 0)) nearest)]
    (knn-predict votes)))
