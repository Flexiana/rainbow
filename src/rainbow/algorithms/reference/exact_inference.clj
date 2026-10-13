(ns rainbow.algorithms.reference.exact-inference
  "Executable exact Bayesian inference by enumeration. A marginal is the exact
  rational sum, over every value of a finite hidden variable, of the factored
  joint `likelihood(hidden) * prior(hidden)`. This matches the proved Rainbow
  definition; all arithmetic is exact.")

(defn- exact-nonnegative-rational? [value]
  (and (rational? value) (not (neg? value))))

(defn joint
  "The factored joint entry for a hidden value: likelihood times prior."
  [prior likelihood hidden]
  (* (likelihood hidden) (prior hidden)))

(defn marginal
  "Marginalize the hidden variable over its finite grid by enumeration."
  [grid prior likelihood]
  (when-not (and (sequential? grid) (ifn? prior) (ifn? likelihood))
    (throw (ex-info "Inference needs a grid and prior/likelihood functions"
                    {:grid grid})))
  (let [total (reduce + 0 (map #(joint prior likelihood %) grid))]
    (when-not (exact-nonnegative-rational? total)
      (throw (ex-info "Marginal is not an exact nonnegative rational"
                      {:total total})))
    total))
