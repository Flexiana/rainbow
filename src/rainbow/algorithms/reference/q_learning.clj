(ns rainbow.algorithms.reference.q-learning
  "Executable exact-rational temporal-difference (Q-learning) updates. The
  temporal-difference error is `reward + discount * next - current` and the
  update nudges the estimate by the rate-scaled error. With exact rationals the
  error can be negative, matching the proved signed-rational Rainbow definition.")

(defn td-error
  "The temporal-difference error reward + discount*next - current."
  [reward discount next current]
  (- (+ reward (* discount next)) current))

(defn q-update
  "One Q-learning update: current + rate * (temporal-difference error)."
  [rate reward discount next current]
  (+ current (* rate (td-error reward discount next current))))

(defn q-iterate
  "Repeatedly apply the same Q-update from an initial estimate."
  [rate reward discount next steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Q-learning steps must be a natural integer" {:steps steps})))
  (nth (iterate #(q-update rate reward discount next %) initial) steps))

(defn trajectory
  "The first steps+1 exact Q-value iterates as a vector."
  [rate reward discount next initial steps]
  (mapv #(q-iterate rate reward discount next % initial) (range (inc steps))))
