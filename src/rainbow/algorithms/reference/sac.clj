(ns rainbow.algorithms.reference.sac
  "Executable Soft Actor-Critic soft value, matching the proved Rainbow
  definition.")

(defn soft-value
  "Entropy-regularized soft value: reward + alpha*entropy."
  [reward alpha entropy]
  (+ reward (* alpha entropy)))

(defn soft-q-target
  "Soft Q target: reward + gamma*(V(next) + alpha*entropy(next))."
  [reward gamma next-value alpha next-entropy]
  (+ reward (* gamma (soft-value next-value alpha next-entropy))))
