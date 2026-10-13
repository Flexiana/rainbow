(ns rainbow.algorithms.reference.finite-matrix-multiply
  "Executable exact reference semantics for native row-major matrix multiply."
  (:require [rainbow.algorithms.reference.finite-matrix :as matrix]
            [rainbow.algorithms.reference.finite-matrix-transpose :as transpose]))

(defn multiply
  "Multiply row-major matrices using exact dot products.

  Rectangular compatible matrices receive ordinary multiplication. Ragged or
  dimension-mismatched inputs follow the proved total transpose/dot truncation
  semantics."
  [left right]
  (let [columns (transpose/transpose right)]
    (mapv #(matrix/vector-multiply columns %) left)))
