(ns rainbow.algorithms.reference.word-break
  "Executable word break DP, matching the proved per-split success decision.")

(defn split-works? [prefix-breakable? suffix-is-word?]
  (and prefix-breakable? suffix-is-word?))

(defn word-break?
  "True iff s can be segmented into words from the dictionary set."
  [s dict]
  (let [n (count s)]
    (loop [i 1, breakable (assoc (vec (repeat (inc n) false)) 0 true)]
      (if (> i n)
        (breakable n)
        (recur (inc i)
               (assoc breakable i
                      (boolean
                       (some (fn [j]
                               (split-works? (breakable j)
                                             (contains? dict (subs s j i))))
                             (range i)))))))))
