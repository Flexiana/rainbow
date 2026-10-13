(ns rainbow.algorithms.reference.triangular
  "Executable triangular numbers (AHoF). The recurrence matches the proved
  Rainbow definition; `closed-form` computes the same value by Gauss's formula
  n(n+1)/2, and `pair-count` is its combinatorial reading.")

(defn number
  "T(n) = 0 + 1 + ... + n."
  [n]
  (reduce + 0 (range (inc n))))

(defn closed-form
  "Gauss closed form: n(n+1)/2."
  [n]
  (quot (* n (inc n)) 2))

(defn pair-count
  "Number of unordered pairs among n+1 items = T(n)."
  [n]
  (number n))
