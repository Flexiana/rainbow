(ns rainbow.algorithms.reference.counting-sort
  "Executable counting sort, matching the proved cumulative-counts definition."
  (:require [rainbow.algorithms.reference.prefix-sum :as prefix-sum]))

(defn cumulative-counts [counts] (prefix-sum/cumulative-sum counts))

(defn counting-sort
  "Stable counting sort of non-negative integer keys in [0, k)."
  [xs k]
  (let [counts (reduce (fn [c x] (update c x inc)) (vec (repeat k 0)) xs)
        offsets (vec (cumulative-counts counts))]
    (loop [items (reverse xs), offsets offsets, out (vec (repeat (count xs) nil))]
      (if (empty? items)
        out
        (let [x (first items)
              pos (dec (offsets x))]
          (recur (rest items) (update offsets x dec) (assoc out pos x)))))))
