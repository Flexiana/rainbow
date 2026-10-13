(ns rainbow.algorithms.reference.bucket-sort
  "Executable bucket sort, matching the proved bucket-ordering decision.")

(defn bucket-precedes? [bucket-a bucket-b] (<= bucket-a bucket-b))

(defn bucket-sort
  "Bucket-sort values in [0, 1) into k buckets, sorting each and concatenating the
  buckets in increasing index order."
  [xs k]
  (let [buckets (reduce (fn [b x]
                          (update b (min (dec k) (int (* x k))) conj x))
                        (vec (repeat k [])) xs)]
    (vec (mapcat sort (for [i (range k) :when (bucket-precedes? 0 i)] (buckets i))))))
