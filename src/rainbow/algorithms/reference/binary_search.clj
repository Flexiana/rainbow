(ns rainbow.algorithms.reference.binary-search
  "Executable binary search, matching the proved Rainbow branch rule.")

(defn search-left? [target midpoint] (<= target midpoint))

(defn binary-search
  "Index of target in a sorted vector, or nil if absent."
  [v target]
  (loop [lo 0, hi (dec (count v))]
    (when (<= lo hi)
      (let [mid (quot (+ lo hi) 2), m (v mid)]
        (cond
          (= m target) mid
          (search-left? target m) (recur lo (dec mid))
          :else (recur (inc mid) hi))))))
