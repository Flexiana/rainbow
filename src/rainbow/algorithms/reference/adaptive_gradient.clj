(ns rainbow.algorithms.reference.adaptive-gradient
  "Executable exact-rational AdaGrad adaptive rate (AHoF O21). The square-root
  witness and adaptive rate match the proved Rainbow definitions; the full
  per-parameter update around the rate is the executable optimizer concern."
  (:require [clojure.math :as math]))

(defn square-root?
  "True when root is an exact square root of radicand."
  [radicand root]
  (= radicand (* root root)))

(defn rate
  "Adaptive learning rate: base-rate / sqrt(accumulator). Given an exact root,
  this is base-rate / root."
  [base-rate root]
  (/ base-rate root))

(defn adaptive-step
  "One AdaGrad scalar step with an exact perfect-square accumulator:
  x' = x - (base-rate / root) * gradient, where root*root = accumulator."
  [x gradient base-rate accumulator]
  (let [root (long (math/sqrt accumulator))]
    (assert (square-root? accumulator root) "accumulator must be a perfect square")
    (- x (* (rate base-rate root) gradient))))
