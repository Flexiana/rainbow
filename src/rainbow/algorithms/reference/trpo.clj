(ns rainbow.algorithms.reference.trpo
  "Executable TRPO trust-region admissibility test, matching the proved Rainbow
  definition. A policy update is admitted iff its KL divergence is within the
  trust radius.")

(defn within-trust-region?
  "True iff the KL divergence is within the trust radius delta."
  [kl delta]
  (<= kl delta))

(defn admit-step
  "Backtracking line search: largest admissible fraction of the full step whose
  KL stays within delta, given a kl-of-fraction function."
  [kl-of-fraction delta fractions]
  (first (filter #(within-trust-region? (kl-of-fraction %) delta) fractions)))
