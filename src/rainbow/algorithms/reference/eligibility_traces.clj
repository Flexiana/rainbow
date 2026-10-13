(ns rainbow.algorithms.reference.eligibility-traces
  "Executable exact-rational eligibility traces (TD(lambda)). The eligibility trace
  decays and increments for the visited state; on a TD error the value is updated
  in proportion to its trace. Matches the proved Rainbow definitions.")

(defn trace-update
  "Decay the trace by the discount-times-lambda factor and increment for the
  visited state."
  [decay trace]
  (+ (* decay trace) 1))

(defn trace-weighted-update
  "Update the value by rate times the trace times the TD error."
  [rate trace td-error value]
  (+ value (* (* rate trace) td-error)))
