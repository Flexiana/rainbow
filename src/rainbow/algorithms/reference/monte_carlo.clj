(ns rainbow.algorithms.reference.monte-carlo
  "Executable exact-rational direct Monte Carlo estimation. Given a sequence of
  sample outcomes (true = failure), the empirical failure frequency is the exact
  rational count-of-failures divided by the sample size, matching the proved
  Rainbow definition.")

(defn failure-count
  "The number of failing samples."
  [samples]
  (count (filter true? samples)))

(defn failure-frequency
  "The empirical failure probability: failures over the sample size."
  [samples]
  (let [n (count samples)]
    (when (zero? n)
      (throw (ex-info "Cannot estimate from an empty sample" {})))
    (/ (failure-count samples) n)))
