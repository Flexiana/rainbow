(ns rainbow.algorithms.reference.dutch-flag
  "Executable Dutch-flag 3-way partition, matching the proved low-region routing.")

(defn goes-low? [element pivot-minus-one] (<= element pivot-minus-one))

(defn three-way-partition
  "Partition xs around pivot into [<pivot =pivot >pivot] (stable order not kept;
  returns the concatenated 3-way-sorted vector)."
  [xs pivot]
  (let [pm1 (dec pivot)]
    (loop [items xs, low [], mid [], high []]
      (if (empty? items)
        (vec (concat low mid high))
        (let [x (first items)]
          (cond
            (goes-low? x pm1) (recur (rest items) (conj low x) mid high)
            (= x pivot) (recur (rest items) low (conj mid x) high)
            :else (recur (rest items) low mid (conj high x))))))))
