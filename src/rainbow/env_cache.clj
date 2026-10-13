(ns rainbow.env-cache
  "Process-level memo for CHECKED environments, so a batch of gates verifies the
  same declarations once instead of once per namespace.

  WHY THIS IS SOUND, AND WHAT IT DOES NOT DO. It memoizes nothing about proving:
  the kernel still checks every declaration, in this process, before any cached
  value exists. The only thing removed is REPETITION -- 3890 test namespaces each
  hold their own `(delay (load-checkpoint ...))` and each rebuilds the same base
  and the same shared extensions, so a run of N namespaces in one JVM pays the
  same verified work N times.

  Measured, and the first version of this docstring got it wrong: replaying the base
  checkpoint (13.7 s) is ALREADY memoized -- `checkpoint/load-checkpoint` keeps a
  replay-cache keyed by path and mtime -- so the base was never being repeated. What
  IS repeated is the shared extension chain, because `support/extend-with` does not
  skip already-installed declarations: the `decide-equal` step costs 34.5 s, and
  every namespace whose chain starts with it pays again. That is the saving here:
  about 34.5 s per extra namespace in a batch, not the 48 s first claimed.

  The cache lives in one process and dies with it. Nothing is written to disk and
  nothing is trusted across runs, so the trusted base is untouched -- this is not
  an `.olean`-style checked-artifact cache, which WOULD widen it and is a separate
  decision.

  It also cannot help a single-namespace gate: one environment built once is the
  floor, and for a family that floor is dominated by checking the family's OWN
  theorems (63 s of the 125 s measured for aggplan), which is exactly what the
  gate exists to do."
  (:require [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]))

(def default-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(defonce ^:private cache (atom {}))

(defn- replayed-base [path]
  (let [checkpoint (checkpoint/load-checkpoint path)]
    (when-not (= :replayed (:status checkpoint))
      (throw (ex-info "checkpoint did not replay" {:path path :status (:status checkpoint)})))
    (:environment checkpoint)))

(defn base
  "The replayed, verified base environment for a checkpoint path. Memoized per
  process: the replay kernel-checks every declaration the first time and the same
  verified value is handed out afterwards."
  ([] (base default-checkpoint))
  ([path]
   (let [key [:base path]]
     (or (get @cache key)
         (let [built (replayed-base path)]
           (swap! cache assoc key built)
           built)))))

(defn extend-chain
  "Fold `extenders` (functions environment -> environment, typically a module's
  `extend-environment`) over the base, memoizing EVERY PREFIX. Two chains sharing
  a prefix -- and nearly all of them share `decide-equal` -- build that prefix
  once.

  Keyed by the extender objects themselves, so passing the same vars gives the
  same key. Pass vars (`#'m/extend-environment`) rather than anonymous wrappers if
  you want the sharing to bite."
  ([extenders] (extend-chain default-checkpoint extenders))
  ([path extenders]
   (reduce (fn [env extender]
             (let [key [:step path (environment/environment-id env) extender]]
               (or (get @cache key)
                   (let [built (extender env)]
                     (swap! cache assoc key built)
                     built))))
           (base path)
           extenders)))

(defn stats
  "What the cache holds -- for a gate that wants to report how much repetition it
  avoided."
  []
  (let [held @cache]
    {:entries (count held)
     :bases (count (filter #(= :base (first %)) (keys held)))
     :steps (count (filter #(= :step (first %)) (keys held)))}))

(defn reset-cache!
  "Drop everything. For a test that wants a cold build."
  []
  (reset! cache {}))
