(ns rainbow.algorithms.reference.quickselect
  "Executable quickselect, matching the proved recursion-side decision.")

(defn recurse-left? [target-rank pivot-rank] (<= target-rank pivot-rank))

(defn quickselect
  "The k-th smallest (1-indexed) element of xs."
  [xs k]
  (let [pivot (nth xs (quot (count xs) 2))
        lt (filter #(< % pivot) xs)
        eq (filter #(= % pivot) xs)
        gt (filter #(> % pivot) xs)
        nlt (count lt)
        pivot-rank (+ nlt (count eq))]
    (cond
      (<= k nlt) (quickselect lt k)
      (recurse-left? k pivot-rank) pivot
      :else (quickselect gt (- k pivot-rank)))))
