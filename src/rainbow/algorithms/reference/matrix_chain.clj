(ns rainbow.algorithms.reference.matrix-chain
  "Executable matrix-chain-multiplication DP, matching the proved Rainbow rules.")

(defn split-cost [left right multiply] (+ left right multiply))

(defn better-split [current-best candidate]
  (if (<= candidate current-best) candidate current-best))

(defn min-mults
  "Minimum scalar multiplications to multiply matrices with dimension chain dims
  (length n+1 for n matrices)."
  [dims]
  (let [n (dec (count dims))
        dp (atom {})]
    (doseq [i (range n)] (swap! dp assoc [i i] 0))
    (doseq [len (range 2 (inc n)), i (range (- n len -1))]
      (let [j (+ i len -1)]
        (swap! dp assoc [i j]
               (reduce (fn [best k]
                         (better-split
                          best
                          (split-cost (@dp [i k]) (@dp [(inc k) j])
                                      (* (dims i) (dims (inc k)) (dims (inc j))))))
                       1e18 (range i j)))))
    (@dp [0 (dec n)])))
