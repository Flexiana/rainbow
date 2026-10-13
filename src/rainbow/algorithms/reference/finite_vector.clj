(ns rainbow.algorithms.reference.finite-vector
  "Executable exact-rational finite vectors: lists of components with elementwise
  addition, negation, subtraction, and scalar scaling. Matches the proved Rainbow
  definitions.")

(defn add
  "Elementwise sum of two vectors (truncating at the shorter length)."
  [left right]
  (mapv + left right))

(defn negate
  "Negate every component."
  [components]
  (mapv - components))

(defn scale
  "Scale every component by a factor."
  [rate components]
  (mapv #(* rate %) components))

(defn subtract
  "Elementwise difference: add the negation."
  [left right]
  (add left (negate right)))
