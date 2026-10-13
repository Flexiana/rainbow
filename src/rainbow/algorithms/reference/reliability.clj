(ns rainbow.algorithms.reference.reliability
  "Executable series-system reliability, matching the proved Rainbow definitions."
  (:require [rainbow.algorithms.reference.list-product :as list-product]))

(defn series-reliability
  "Reliability of a series system = product of component reliabilities."
  [reliabilities]
  (list-product/list-product reliabilities))

(defn meets-requirement?
  "True iff the system reliability meets the target threshold."
  [reliability threshold]
  (<= threshold reliability))

(defn parallel-reliability
  "Reliability of a parallel (redundant) system = 1 - product(1 - r_i)."
  [reliabilities]
  (- 1 (list-product/list-product (map #(- 1 %) reliabilities))))
