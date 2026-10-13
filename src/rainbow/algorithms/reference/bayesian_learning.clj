(ns rainbow.algorithms.reference.bayesian-learning
  "Executable exact-rational Bayesian parameter learning: the posterior mass is
  the prior folded through the data, each datum multiplying the running mass by
  its likelihood. Matches the proved Rainbow definitions.")

(defn bayesian-update
  "One Bayesian update: multiply the current mass by a likelihood."
  [mass likelihood]
  (* mass likelihood))

(defn posterior
  "Fold the data likelihoods through the prior to the posterior mass."
  [prior likelihoods]
  (reduce bayesian-update prior likelihoods))
