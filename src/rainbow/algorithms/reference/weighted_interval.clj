(ns rainbow.algorithms.reference.weighted-interval
  "Executable weighted interval scheduling DP, matching the proved cell rule.")

(defn cell [include-value exclude-value]
  (if (<= include-value exclude-value) exclude-value include-value))

(defn max-weight
  "Max total weight of compatible intervals [start finish weight]."
  [intervals]
  (let [iv (vec (sort-by second intervals))
        n (count iv)
        p (fn [j] (or (last (keep-indexed
                             (fn [i [_ f _]] (when (<= f (first (iv j))) i))
                             (subvec iv 0 j))) -1))]
    (loop [j 0, dp [0]]
      (if (= j n)
        (last dp)
        (let [[_ _ w] (iv j)
              incl (+ w (dp (inc (p j))))
              excl (dp j)]
          (recur (inc j) (conj dp (cell incl excl))))))))
