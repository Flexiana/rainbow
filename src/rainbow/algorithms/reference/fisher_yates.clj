(ns rainbow.algorithms.reference.fisher-yates
  "Executable Fisher-Yates shuffle, matching the proved valid-swap rule.")

(defn valid-swap? [j i] (<= j i))

(defn shuffle-with
  "In-place Fisher-Yates shuffle using a deterministic rng (i -> j in [0,i])."
  [xs rng]
  (let [v (vec xs)]
    (loop [v v, i (dec (count v))]
      (if (<= i 0)
        v
        (let [j (rng i)]
          (if (valid-swap? j i)
            (recur (assoc v i (v j) j (v i)) (dec i))
            (recur v (dec i))))))))

(defn is-permutation?
  "Check the shuffle is a permutation (same multiset)."
  [xs ys]
  (= (frequencies xs) (frequencies ys)))
