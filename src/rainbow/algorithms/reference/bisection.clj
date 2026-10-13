(ns rainbow.algorithms.reference.bisection
  "Executable exact-rational bisection bracket search. The probe of a bracket
  [lo, hi] is its midpoint (lo + hi) / 2; narrowing keeps the lower or upper half
  based on a boolean test, halving the interval. Matches the proved Rainbow
  definitions.")

(defn midpoint
  "The exact midpoint of a bracket."
  [lo hi]
  (/ (+ lo hi) 2))

(defn narrow
  "Narrow the bracket to its lower or upper half by the midpoint probe."
  [keep-lower? lo hi]
  (let [m (midpoint lo hi)]
    (if keep-lower? [lo m] [m hi])))

(defn width
  "The exact width of a bracket."
  [[lo hi]]
  (- hi lo))
