(ns rainbow.algorithms.reference.quicksort
  "Executable quicksort, matching the proved Rainbow partition decision.")

(defn goes-left? [element pivot] (<= element pivot))

(defn quicksort
  "Quicksort of a sequence."
  [xs]
  (if (<= (count xs) 1)
    (vec xs)
    (let [pivot (first xs)
          rest-xs (rest xs)
          left (filter #(goes-left? % pivot) rest-xs)
          right (remove #(goes-left? % pivot) rest-xs)]
      (vec (concat (quicksort left) [pivot] (quicksort right))))))
