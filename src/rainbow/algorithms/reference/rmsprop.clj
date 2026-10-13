(ns rainbow.algorithms.reference.rmsprop
  "Executable exact-rational RMSProp accumulator (AHoF O22). The decayed
  squared-gradient accumulator matches the proved Rainbow definition; the
  adaptive rate reuses AdaGrad (base / sqrt(accumulator))."
  (:require [clojure.math :as math]))

(defn accumulate
  "Decayed squared-gradient average: retain*prev + fresh*gradient^2."
  [retain fresh prev grad-squared]
  (+ (* retain prev) (* fresh grad-squared)))

(defn rate
  "Adaptive rate: base-rate / sqrt(accumulator) on perfect-square accumulators."
  [base-rate accumulator]
  (let [root (long (math/sqrt accumulator))]
    (assert (= accumulator (* root root)) "accumulator must be a perfect square")
    (/ base-rate root)))
