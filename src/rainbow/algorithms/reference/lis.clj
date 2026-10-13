(ns rainbow.algorithms.reference.lis
  "Executable longest increasing subsequence (patience sorting), matching the
  proved extend decision.")

(defn extends? [tail element] (<= tail element))

(defn lis-length
  "Length of the longest strictly-increasing subsequence."
  [xs]
  (count
   (reduce
    (fn [tails x]
      ;; replace the first tail >= x (strict LIS), else extend
      (let [i (count (take-while #(< % x) tails))]
        (if (extends? (count tails) i)   ; i == count tails means x is a new max
          (conj tails x)
          (assoc tails i x))))
    []
    xs)))
