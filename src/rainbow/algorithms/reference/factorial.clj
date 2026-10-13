(ns rainbow.algorithms.reference.factorial
  "Executable factorial and derived combinatorial counts (AHoF). The factorial
  matches the proved Rainbow definition; permutations and combinations are the
  design-space sizes it underlies.")

(defn fact
  "n! -- the number of permutations of n items."
  [n]
  (reduce * 1 (range 1 (inc n))))

(defn permutations
  "n! / (n-k)! -- ordered selections of k from n."
  [n k]
  (/ (fact n) (fact (- n k))))

(defn combinations
  "n choose k = n! / (k! (n-k)!) -- unordered selections of k from n."
  [n k]
  (/ (fact n) (* (fact k) (fact (- n k)))))
