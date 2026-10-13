(ns rainbow.module
  "Declarative module dependencies.

  A proof module names the modules it depends on in `deps` (a vector of namespace
  symbols) and adds only its own declarations in `install` (environment ->
  environment). `install-module` installs a module together with everything it
  depends on, each module exactly once and in dependency order: every module after
  all of its dependencies, siblings in the order they are listed.

  The environment remembers which modules it has installed under ::installed. That
  key is bookkeeping only: an environment's identity is computed from its
  declarations, so it is unaffected. Re-installing a module that an environment
  already has is a no-op, which is what makes a dependency shared by many modules
  cost one install instead of one per path to it.

  The kernel still checks every declaration, once. Nothing here is trusted: a
  missing dependency shows up as the kernel rejecting a declaration that names an
  unknown constant."
  (:require [clojure.set :as set]))

(defn- module-var [ns-sym var-sym]
  (require ns-sym)
  (ns-resolve ns-sym var-sym))

(defn deps
  "The modules ns-sym declares it depends on."
  [ns-sym]
  (vec (some-> (module-var ns-sym 'deps) deref)))

(defn order
  "Every module reachable from roots, each once, each after all of its dependencies.
  Throws on a dependency cycle, naming it."
  [roots]
  (loop [stack (mapv (fn [r] [r false]) (rseq (vec roots)))
         visiting #{}
         done #{}
         out []]
    (if-let [[n expanded?] (peek stack)]
      (let [stack (pop stack)]
        (cond
          (done n) (recur stack visiting done out)
          expanded? (recur stack (disj visiting n) (conj done n) (conj out n))
          (visiting n) (throw (ex-info "module dependency cycle" {:module n :path visiting}))
          :else (recur (into (conj stack [n true])
                             (map (fn [d] [d false]) (rseq (deps n))))
                       (conj visiting n) done out)))
      out)))

(defn installed
  "The modules an environment has installed through this namespace."
  [environment]
  (::installed environment #{}))

(defn install-module
  "Installs ns-sym and its dependencies into environment, skipping modules the
  environment already has."
  [environment ns-sym]
  (reduce (fn [env n]
            (if (contains? (installed env) n)
              env
              ;; A module not yet converted to declared dependencies has no install: its
              ;; extend-environment installs its own dependencies, as before.
              (let [install (or (module-var n 'install) (module-var n 'extend-environment))]
                (when-not install
                  (throw (ex-info "module has neither install nor extend-environment" {:module n})))
                (update (install env) ::installed (fnil conj #{}) n))))
          environment
          (order [ns-sym])))
