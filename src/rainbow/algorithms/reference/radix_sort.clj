(ns rainbow.algorithms.reference.radix-sort
  "Executable LSD radix sort, matching the proved per-digit order.")

(defn digit-precedes? [digit-a digit-b] (<= digit-a digit-b))

(defn- digit [x d] (mod (quot x (long (Math/pow 10 d))) 10))

(defn- counting-by-digit [xs d]
  ;; stable bucket sort by the d-th digit
  (let [buckets (reduce (fn [b x] (update b (digit x d) (fnil conj []) x))
                        (vec (repeat 10 [])) xs)]
    (vec (mapcat identity buckets))))

(defn radix-sort
  "LSD radix sort of non-negative integers with up-to `digits` digits."
  [xs digits]
  (reduce counting-by-digit (vec xs) (range digits)))
