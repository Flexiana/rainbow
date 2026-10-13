(ns rainbow.algorithms.reference.naive-bayes
  "Executable Naive Bayes scoring and classification, matching the proved Rainbow
  definitions."
  (:require [rainbow.algorithms.reference.list-product :as list-product]
            [rainbow.algorithms.reference.argmax-index :as argmax-index]))

(defn nb-score
  "Unnormalized class posterior: prior * product of feature likelihoods."
  [prior likelihoods]
  (* prior (list-product/list-product likelihoods)))

(defn classify
  "Predicted class = argmax of the class scores."
  [scores]
  (argmax-index/argmax-index scores))

(defn predict
  "Classify a feature vector given per-class (prior, likelihoods)."
  [class-models]
  (classify (map (fn [[prior likelihoods]] (nb-score prior likelihoods))
                 class-models)))
