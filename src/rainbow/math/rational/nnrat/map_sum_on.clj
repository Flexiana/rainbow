(ns rainbow.math.rational.nnrat.map-sum-on
  "Compatibility entry point for the canonical member-restricted sum theorem.
  Master's metric-separation installer is authoritative. The independently
  written proof is retained only as a kernel-checked test fixture."
  (:require [rainbow.module :as module]
            [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.math.milestone-support :as support]))

(def map-sum-monotone-on-spec metric/map-sum-monotone-on-spec)
(def theorem-specs [map-sum-monotone-on-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.metric-separation])

(defn install
  "Adds this module's own declarations."
  [env]
  env)

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.map-sum-on))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
