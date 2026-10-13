(ns rainbow.math.rational.nnrat.map-sum-on
  "Compatibility entry point for the canonical member-restricted sum theorem.
  Master's metric-separation installer is authoritative. The independently
  written proof is retained only as a kernel-checked test fixture."
  (:require [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.math.milestone-support :as support]))

(def map-sum-monotone-on-spec metric/map-sum-monotone-on-spec)
(def theorem-specs [map-sum-monotone-on-spec])
(defn extend-environment [env] (metric/extend-environment env))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
