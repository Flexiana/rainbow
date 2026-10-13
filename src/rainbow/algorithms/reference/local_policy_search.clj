(ns rainbow.algorithms.reference.local-policy-search
  "Executable Local Policy Search (AHoF D40). The improvement step matches the
  proved Rainbow definition; `search` runs hill climbing: perturb, evaluate, keep
  the better policy, for a number of iterations.")

(defn improve
  "Keep the higher-scoring of the incumbent and neighbor values."
  [incumbent neighbor]
  (max incumbent neighbor))

(defn search
  "Local policy search maximizing `value`. `perturb` proposes a neighbor policy.
  Returns the best policy found after `steps` iterations."
  [value perturb policy steps]
  (loop [policy policy remaining steps]
    (if (zero? remaining)
      policy
      (let [neighbor (perturb policy)]
        (recur (if (> (value neighbor) (value policy)) neighbor policy)
               (dec remaining))))))
