(ns rainbow.algorithms.reference.golden-section-search
  "Executable exact-rational Golden Section Search reduction step: compare the two
  interior probe values and keep the side with the smaller value. Matches the proved
  Rainbow definitions.")

(defn keep-left?
  "Keep the left sub-interval when the left interior value is at most the right."
  [fc fd]
  (<= fc fd))

(defn retained-min
  "The retained interior value: the minimum of the two probe values."
  [fc fd]
  (if (<= fc fd) fc fd))
