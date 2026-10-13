(ns rainbow.algorithms.reference.lcs
  "Executable LCS DP, matching the proved Rainbow cell recurrence.")

(defn cell [matched? diag left up]
  (if matched? (+ 1 diag) (max left up)))

(defn lcs-length
  "Length of the longest common subsequence of sequences a and b."
  [a b]
  (let [a (vec a) b (vec b) m (count a) n (count b)]
    (loop [i 0, prev (vec (repeat (inc n) 0))]
      (if (= i m)
        (last prev)
        (recur (inc i)
               (reduce (fn [cur j]
                         (conj cur (cell (= (a i) (b j))
                                         (prev j) (peek cur) (prev (inc j)))))
                       [0] (range n)))))))
