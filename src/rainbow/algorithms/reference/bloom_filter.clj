(ns rainbow.algorithms.reference.bloom-filter
  "Executable bloom filter, matching the proved all-bits-set membership.")

(defn possibly-present? [bit-a bit-b] (and bit-a bit-b))

(defn- hashes [x k m]
  (map #(mod (+ (hash x) (* % 2654435761)) m) (range k)))

(defn add
  "Set the k hash-indexed bits for x in an m-bit filter (a set of indices)."
  [bits x k m]
  (into bits (hashes x k m)))

(defn contains-maybe?
  "True iff all k of x's bits are set (possibly present); false = definitely
  absent."
  [bits x k m]
  (reduce (fn [acc i] (possibly-present? acc (contains? bits i)))
          true (hashes x k m)))
