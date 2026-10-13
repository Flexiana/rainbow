(ns rainbow.algorithms.reference.maximum-likelihood
  "Executable exact-rational maximum likelihood estimation. Each model is scored
  by the sum of its per-datum log-likelihoods; maximum likelihood prefers the
  model with the larger total. Matches the proved Rainbow definitions.")

(defn log-likelihood-total
  "The total log-likelihood: sum of the per-datum log-likelihoods."
  [scores]
  (reduce + 0 scores))

(defn mle-prefers?
  "Maximum likelihood prefers the first model when its total is at least the
  second's."
  [total-a total-b]
  (<= total-b total-a))

(defn estimate
  "Select the model with the larger total log-likelihood."
  [scores-a scores-b]
  (let [ta (log-likelihood-total scores-a)
        tb (log-likelihood-total scores-b)]
    (if (mle-prefers? ta tb) :model-a :model-b)))
