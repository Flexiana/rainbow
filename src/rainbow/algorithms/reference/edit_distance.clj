(ns rainbow.algorithms.reference.edit-distance
  "Executable exact-rational edit distance / Levenshtein (AHoF). The DP cell
  matches the proved Rainbow definition; `distance` fills the full cost matrix to
  align two sequences with unit operation costs.")

(defn cell
  "Cheapest of the three edit options reaching a cell."
  [del ins sub]
  (min del (min ins sub)))

(defn distance
  "Levenshtein edit distance between two sequences (unit costs)."
  [a b]
  (let [a (vec a) b (vec b) m (count a) n (count b)]
    (loop [row (vec (range (inc n))) i 1]
      (if (> i m)
        (last row)
        (let [new-row
              (reduce
               (fn [r j]
                 (conj r (cell (inc (nth r (dec j)))          ; deletion
                               (inc (nth row j))              ; insertion
                               (+ (nth row (dec j))           ; match/substitute
                                  (if (= (nth a (dec i)) (nth b (dec j))) 0 1)))))
               [i]
               (range 1 (inc n)))]
          (recur new-row (inc i)))))))
