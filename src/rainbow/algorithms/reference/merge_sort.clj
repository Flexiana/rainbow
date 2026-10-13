(ns rainbow.algorithms.reference.merge-sort
  "Executable merge sort, matching the proved Rainbow merge decision.")

(defn take-from-left? [left-head right-head] (<= left-head right-head))

(defn merge-runs
  "Merge two sorted sequences into one sorted sequence (stable)."
  [a b]
  (loop [a a, b b, out []]
    (cond
      (empty? a) (into out b)
      (empty? b) (into out a)
      (take-from-left? (first a) (first b)) (recur (rest a) b (conj out (first a)))
      :else (recur a (rest b) (conj out (first b))))))

(defn merge-sort
  "Stable merge sort of a sequence."
  [xs]
  (if (<= (count xs) 1)
    (vec xs)
    (let [[l r] (split-at (quot (count xs) 2) xs)]
      (merge-runs (merge-sort l) (merge-sort r)))))
