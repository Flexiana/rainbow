(ns rainbow.algorithms.reference.gradient-ascent
  "Executable exact-rational bounded fixed-rate gradient ascent. The gradient is
  a pluggable function; each step is `point + rate * (gradient point)`. All
  arithmetic is exact so the reference matches the proved Rainbow definition.")

(defn- exact-nonnegative-rational? [value]
  (and (rational? value) (not (neg? value))))

(defn ascent-step
  "One exact gradient-ascent update."
  [gradient rate point]
  (+ point (* rate (gradient point))))

(defn ascent-iterate
  "Run a bounded number of exact gradient-ascent steps from `initial`."
  [gradient rate steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Gradient-ascent steps must be a natural integer"
                    {:steps steps})))
  (when-not (and (ifn? gradient) (exact-nonnegative-rational? rate)
                 (exact-nonnegative-rational? initial))
    (throw (ex-info "Gradient ascent needs a gradient fn and exact rate/initial"
                    {:rate rate :initial initial})))
  (nth (iterate #(ascent-step gradient rate %) initial) steps))

(defn trajectory
  "The first `steps`+1 exact iterates as a vector."
  [gradient rate initial steps]
  (mapv #(ascent-iterate gradient rate % initial) (range (inc steps))))
