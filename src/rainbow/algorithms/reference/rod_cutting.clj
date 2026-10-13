(ns rainbow.algorithms.reference.rod-cutting
  "Executable rod-cutting DP, matching the proved Rainbow cell rule.")

(defn cell [current-best cut-revenue]
  (if (<= current-best cut-revenue) cut-revenue current-best))

(defn max-revenue
  "Max revenue cutting a rod of length n; prices is a vector where prices[i] is
  the price of a piece of length i+1."
  [n prices]
  (let [price (fn [len] (get prices (dec len) 0))]
    (loop [len 1, rev [0]]
      (if (> len n)
        (last rev)
        (recur (inc len)
               (conj rev (reduce (fn [best i]
                                   (cell best (+ (price i) (rev (- len i)))))
                                 0 (range 1 (inc len)))))))))
