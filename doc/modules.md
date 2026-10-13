# Proof modules

A proof module is a Clojure namespace that adds declarations to an environment.
Its shape is data, so the dependency graph of the whole corpus can be read,
checked and installed without running anything first.

```clojure
;; src/rainbow/math/rational/signed/lp_duality_on.clj (abridged)
(ns rainbow.math.rational.signed.lp-duality-on
  "LP weak duality and the optimality certificate, quantified over the rows and ..."
  (:require [rainbow.module :as module] ...))

(def theorem-specs                                   ; the declarations: statement + proof
  [double-counting-spec weak-duality-spec optimality-certificate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-duality rainbow.math.rational.signed.pointwise-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-lp-duality-on theorem-specs)))

(defn extend-environment [checked-environment]      ; installs deps, then the module
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-duality-on))
```

- **`deps`** names the modules whose declarations this one refers to.
- **`install`** adds only this module's own declarations; the kernel checks each
  one on the way in.
- **`extend-environment`** is what callers use. `rainbow.module/install-module`
  walks `deps` recursively, sorts the graph so every module comes after everything
  it depends on, and installs each module exactly once. An environment remembers
  which modules it already has, so installing a module whose dependencies are
  shared with others costs one install per module, not one per path.

## Why it matters

Before 1.0, a module installed its dependencies by calling their installers, which
called theirs. Shared dependencies were installed once per path through the
graph: one module deep in the corpus performed 10,343 module installs for 184
distinct modules, and took over an hour to install on its own. With declared
dependencies the same module installs in minutes, and every proof module in the
repository can be installed and re-checked on its own. That is what the coverage
gate in `test/rainbow/coverage/` does.

## Custom install logic

A few modules need more than adding their own specs: a guarded install of a single
lemma from another module only if it is missing, or a conditional step. That logic
stays inside `install`, after the declared `deps` are in place. Calls from
`install` into another module's `extend-environment` go through the same
installer, so they too install at most once.

Nothing in this layer is trusted. A missing or wrong dependency shows up as the
kernel rejecting a declaration that names an unknown constant.
