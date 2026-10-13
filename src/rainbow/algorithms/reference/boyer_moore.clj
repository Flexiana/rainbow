(ns rainbow.algorithms.reference.boyer-moore
  "Executable Boyer-Moore majority vote, matching the proved majority decision.")

(defn is-majority? [count threshold] (<= threshold count))

(defn majority-element
  "The element appearing more than n/2 times, or nil if none."
  [xs]
  (let [candidate (loop [items xs, cand nil, cnt 0]
                    (if (empty? items)
                      cand
                      (let [x (first items)]
                        (cond
                          (zero? cnt) (recur (rest items) x 1)
                          (= x cand) (recur (rest items) cand (inc cnt))
                          :else (recur (rest items) cand (dec cnt))))))
        cnt (count (filter #(= % candidate) xs))
        threshold (inc (quot (count xs) 2))]
    (when (is-majority? cnt threshold) candidate)))
