(ns rainbow.algorithms.reference.trust-region
  "Executable exact-rational trust region step acceptance. The reduction ratio is
  the actual reduction over the predicted reduction; the step is accepted when the
  ratio is at least the threshold, moving to the candidate, otherwise rejected,
  keeping the current point. Matches the proved Rainbow definitions.")

(defn reduction-ratio
  "Actual reduction over predicted reduction."
  [actual predicted]
  (/ actual predicted))

(defn trust-accept?
  "Accept when the threshold is at most the ratio."
  [threshold ratio]
  (<= threshold ratio))

(defn trust-region-update
  "Move to the candidate if accepted, otherwise keep the current point."
  [accept? candidate current]
  (if accept? candidate current))

(defn step
  "One trust region acceptance step over a [candidate current] decision."
  [threshold actual predicted candidate current]
  (trust-region-update (trust-accept? threshold (reduction-ratio actual predicted))
                       candidate current))
