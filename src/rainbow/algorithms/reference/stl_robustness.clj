(ns rainbow.algorithms.reference.stl-robustness
  "Executable exact-rational signal-temporal-logic (STL) robustness. Robustness
  is computed by structural recursion over the formula: an atomic margin is a
  signed rational, conjunction takes the minimum, disjunction the maximum, and
  negation the sign flip. A nonnegative robustness means the formula is
  satisfied; a negative one means it is violated. Matches the proved signed
  Rainbow definitions.")

(defn atomic
  "Robustness of an atomic predicate is its (already signed) margin."
  [margin]
  margin)

(defn conjunction
  "Robustness of a conjunction is the minimum of its parts."
  [& robustnesses]
  (apply min robustnesses))

(defn disjunction
  "Robustness of a disjunction is the maximum of its parts."
  [& robustnesses]
  (apply max robustnesses))

(defn negation
  "Robustness of a negation flips the sign."
  [robustness]
  (- robustness))

(defn satisfied?
  "A formula is satisfied when its robustness is nonnegative."
  [robustness]
  (not (neg? robustness)))
