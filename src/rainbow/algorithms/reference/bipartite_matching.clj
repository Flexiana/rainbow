(ns rainbow.algorithms.reference.bipartite-matching
  "Executable maximum bipartite matching (Kuhn's augmenting-path), matching the
  proved augment decision.")

(defn can-match? [v-free? partner-reassignable?]
  (or v-free? partner-reassignable?))

(defn max-matching
  "Maximum matching size. adj: left-vertex -> set of right neighbors. lefts is the
  left vertex set."
  [lefts adj]
  (let [match (atom {})]        ; right -> left
    (letfn [(try-augment [u seen]
              (some (fn [v]
                      (when-not (@seen v)
                        (swap! seen conj v)
                        (let [v-free (not (contains? @match v))
                              reassignable (and (not v-free)
                                                (try-augment (@match v) seen))]
                          (when (can-match? v-free (boolean reassignable))
                            (swap! match assoc v u)
                            true))))
                    (adj u)))]
      (count (filter #(try-augment % (atom #{})) lefts)))))
