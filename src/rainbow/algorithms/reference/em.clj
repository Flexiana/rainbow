(ns rainbow.algorithms.reference.em
  "Executable exact-rational EM algorithm (AHoF D13). The monotone-ascent test
  matches the proved Rainbow definition; `em` iterates E-step/M-step until the
  likelihood stops increasing.")

(defn improves? [next-l current-l] (<= current-l next-l))

(defn em
  "Run EM from `params0`. `step` maps parameters to [next-params likelihood];
  `likelihood-of` gives the current likelihood. Iterates until the likelihood
  stops strictly increasing or `max-iters` is reached; returns [params likelihood]."
  [step likelihood-of params0 max-iters]
  (loop [params params0, l (likelihood-of params0), iters max-iters]
    (if (zero? iters)
      [params l]
      (let [[next-params next-l] (step params)]
        (if (> next-l l)
          (recur next-params next-l (dec iters))
          [params l])))))
