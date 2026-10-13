(ns rainbow.algorithms.reference.interval-membership
  "Executable exact-rational interval membership: containment in a closed interval
  [lo, hi] and endpoint-wise interval addition. Matches the proved Rainbow
  definitions in rainbow.algorithms.proofs.interval-membership.")

(defn interval-contains?
  "True when x lies in the closed interval [lo, hi]."
  [lo hi x]
  (and (<= lo x) (<= x hi)))

(defn interval-add-endpoint
  "Endpoint of the interval sum [a,b]+[c,d] = [a+c, b+d]."
  [p q]
  (+ p q))
