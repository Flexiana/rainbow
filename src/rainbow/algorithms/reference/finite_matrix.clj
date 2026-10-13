(ns rainbow.algorithms.reference.finite-matrix
  "Executable exact-rational finite matrices matching the proved nested-List
  matrix/vector-multiply definition."
  (:require [rainbow.algorithms.reference.inner-product :as inner]))

(defn vector-multiply
  "Multiply a row-major matrix by a vector using exact dot products.

  Ragged rows retain the native vector convention: each dot product truncates
  at the shorter of the row and input vector."
  [rows values]
  (mapv #(inner/dot % values) rows))
