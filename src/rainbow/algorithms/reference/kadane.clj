(ns rainbow.algorithms.reference.kadane
  "Executable Kadane's maximum subarray, matching the proved extend decision.")

(defn extend? [extended element] (<= element extended))

(defn max-subarray
  "Maximum-sum contiguous subarray sum (supports negative numbers)."
  [xs]
  (loop [items (rest xs), cur (first xs), best (first xs)]
    (if (empty? items)
      best
      (let [x (first items)
            extended (+ cur x)
            cur (if (extend? extended x) extended x)]
        (recur (rest items) cur (max best cur))))))
