(ns rainbow.algorithms.reference.sliding-window
  "Executable sliding window, matching the proved window-validity rule.")

(defn window-valid? [window-value limit] (<= window-value limit))

(defn max-window-sum
  "Maximum sum of any contiguous window of size k."
  [xs k]
  (let [xs (vec xs)
        first-sum (reduce + (subvec xs 0 k))]
    (loop [i k, cur first-sum, best first-sum]
      (if (>= i (count xs))
        best
        (let [cur (+ cur (xs i) (- (xs (- i k))))]
          (recur (inc i) cur (max best cur)))))))

(defn longest-within-budget
  "Length of the longest contiguous subarray whose sum stays within limit
  (non-negative values)."
  [xs limit]
  (loop [lo 0, hi 0, sum 0, best 0]
    (if (>= hi (count xs))
      best
      (let [sum (+ sum (nth xs hi))]
        (if (window-valid? sum limit)
          (recur lo (inc hi) sum (max best (- (inc hi) lo)))
          (recur (inc lo) (inc hi) (- sum (nth xs hi) (nth xs lo)) best))))))
