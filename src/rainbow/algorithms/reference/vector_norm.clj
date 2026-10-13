(ns rainbow.algorithms.reference.vector-norm
  "Executable exact-rational Euclidean vector norm. Matches the proved Rainbow
  definitions; the norm itself is exact only when the squared norm is a perfect
  square."
  (:require [rainbow.algorithms.reference.inner-product :as inner]
            [clojure.math :as math]))

(defn norm-squared
  "The squared Euclidean norm: the inner product of a vector with itself."
  [v]
  (inner/dot v v))

(defn norm
  "The Euclidean norm, exact when the squared norm is a perfect square."
  [v]
  (let [s (norm-squared v)
        r (long (math/sqrt s))]
    (assert (= s (* r r)) "squared norm must be a perfect square")
    r))

(defn cosine-similarity
  "cos(u,v) = <u,v> / (||u|| * ||v||), exact when both norms are exact."
  [u v]
  (/ (inner/dot u v) (* (norm u) (norm v))))
