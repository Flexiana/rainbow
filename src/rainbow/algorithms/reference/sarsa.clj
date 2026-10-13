(ns rainbow.algorithms.reference.sarsa
  "Executable exact-rational SARSA on-policy update. The updated action value is
  the current value plus the learning rate times the TD error, where the TD error
  bootstraps from the value of the action actually taken in the next state.
  Matches the proved Rainbow definitions.")

(defn td-error
  "The temporal-difference error: (reward + discount * next) - current."
  [reward discount next current]
  (- (+ reward (* discount next)) current))

(defn sarsa-update
  "The SARSA update: current value plus rate times the on-policy TD error."
  [rate reward discount next-action-value current]
  (+ current (* rate (td-error reward discount next-action-value current))))
