(ns rainbow.algorithms.reference.f1-score
  "Executable F1 score, matching the proved Rainbow definition.")

(defn f1 [precision recall]
  (/ (* 2 precision recall) (+ precision recall)))

(defn precision [tp fp] (/ tp (+ tp fp)))
(defn recall [tp fn] (/ tp (+ tp fn)))

(defn f1-from-confusion
  "F1 from confusion-matrix counts."
  [tp fp fn]
  (f1 (precision tp fp) (recall tp fn)))
