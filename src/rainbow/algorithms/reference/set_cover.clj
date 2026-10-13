(ns rainbow.algorithms.reference.set-cover
  "Executable greedy set cover, matching the proved Rainbow selection."
  (:require [rainbow.algorithms.reference.argmax-index :as argmax-index]
            [clojure.set :as set]))

(defn greedy-pick
  "Index of the subset covering the most new elements."
  [coverage]
  (argmax-index/argmax-index coverage))

(defn cover
  "Greedy set cover: indices of chosen subsets covering the universe, or nil if
  impossible. subsets is a vector of element-sets; universe is a set."
  [universe subsets]
  (loop [uncovered (set universe), chosen []]
    (if (empty? uncovered)
      chosen
      (let [cov (mapv #(count (set/intersection % uncovered)) subsets)
            i (greedy-pick cov)]
        (if (zero? (cov i))
          nil
          (recur (set/difference uncovered (subsets i)) (conj chosen i)))))))
