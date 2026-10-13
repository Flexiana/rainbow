(ns rainbow.algorithms.reference.interval-arithmetic
  "Executable exact-rational Interval Arithmetic (AHoF V40). Bounds are exact
  rationals; the additive law matches the proved Rainbow definition. The
  containment predicate and width witness the enclosure soundness that the
  reachability propagators rely on.")

(defn make [lo hi] [lo hi])
(defn lower [interval] (first interval))
(defn upper [interval] (second interval))

(defn add
  "[a,b] + [c,d] = [a+c, b+d]."
  [[a b] [c d]]
  [(+ a c) (+ b d)])

(defn width [[lo hi]] (- hi lo))

(defn within?
  "x lies within the enclosure [lo, hi]."
  [[lo hi] x]
  (and (<= lo x) (<= x hi)))

(defn sound-sum?
  "Soundness check: for x in [a,b] and y in [c,d], x + y lies in [a,b]+[c,d]."
  [left right x y]
  (and (within? left x)
       (within? right y)
       (within? (add left right) (+ x y))))
