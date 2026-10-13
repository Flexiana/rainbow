(ns rainbow.algorithms.reference.adaboost
  "Executable AdaBoost weighting, matching the proved Rainbow ordering.")

(defn earns-more-weight? [err-a err-b] (<= err-a err-b))

(defn alpha
  "Weak-learner vote weight from its weighted error."
  [err]
  (* 1/2 (Math/log (/ (- 1 err) err))))

(defn strong-vote
  "Sign of the weighted vote sum(alpha_i * h_i) for weak predictions in {-1,1}."
  [errors weak-votes]
  (let [s (reduce + (map (fn [e h] (* (alpha e) h)) errors weak-votes))]
    (if (pos? s) 1 -1)))
