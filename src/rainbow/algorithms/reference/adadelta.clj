(ns rainbow.algorithms.reference.adadelta
  "Executable exact-rational Adadelta scale (AHoF O23). The learning-rate-free
  RMS ratio matches the proved Rainbow definition; the two decayed accumulators
  and the general sqrt are the executable optimizer's concern."
  (:require [clojure.math :as math]))

(defn square-root?
  "True when root is an exact square root of radicand."
  [radicand root]
  (= radicand (* root root)))

(defn scale
  "Learning-rate-free scale: sqrt(update-accumulator) / sqrt(gradient-accumulator)
  on perfect-square accumulators."
  [update-accum gradient-accum]
  (let [ur (long (math/sqrt update-accum))
        gr (long (math/sqrt gradient-accum))]
    (assert (and (square-root? update-accum ur) (square-root? gradient-accum gr))
            "accumulators must be perfect squares")
    (/ ur gr)))
