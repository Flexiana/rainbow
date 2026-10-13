(ns rainbow.algorithms.reference.thompson
  "Executable Thompson sampling arm selection, matching the proved Rainbow
  definition."
  (:require [rainbow.algorithms.reference.argmax-index :as argmax-index]))

(defn thompson-select
  "Arm with the largest posterior sample."
  [samples]
  (argmax-index/argmax-index samples))

(defn select-from-posteriors
  "Draw one sample per arm (via sampler) and pull the argmax arm."
  [posteriors sampler]
  (thompson-select (map sampler posteriors)))
