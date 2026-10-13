(ns rainbow.algorithms.reference.jaccard-similarity
  "Executable Jaccard similarity, matching the proved Rainbow definition."
  (:require [clojure.set :as set]))

(defn jaccard [intersection-size union-size] (/ intersection-size union-size))

(defn similarity
  "Jaccard similarity of two sets."
  [a b]
  (let [a (set a) b (set b)
        u (count (set/union a b))]
    (if (zero? u) 1 (jaccard (count (set/intersection a b)) u))))
