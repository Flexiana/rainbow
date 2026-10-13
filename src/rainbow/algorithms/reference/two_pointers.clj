(ns rainbow.algorithms.reference.two-pointers
  "Executable two-pointer pair-sum on a sorted array, matching the proved move
  decision.")

(defn shrink-right? [current-sum target] (<= target current-sum))

(defn pair-sum
  "Indices [i j] of a pair in the sorted vector summing to target, or nil."
  [sorted target]
  (loop [i 0, j (dec (count sorted))]
    (if (>= i j)
      nil
      (let [s (+ (sorted i) (sorted j))]
        (cond
          (= s target) [i j]
          (shrink-right? s target) (recur i (dec j))
          :else (recur (inc i) j))))))
