(ns rainbow.math.finite.markov-stationary-iterate
  "A stationary distribution is fixed by every kernel iterate.

  First brick of the convergence half:
  pi stationary implies `kernel-iterate n pi ~ pi` pointwise for every n,
  by induction -- the successor law unfolds one step, the kernel step
  respects mass equivalence, and stationarity closes the ring. No
  contraction premise appears anywhere here; this brick is independent of
  the Dobrushin line and is consumed later when convergence toward the
  stationary target is stated. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def zero-level [:zero])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- mass-type [element] (function/arrow element nnrat))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- succ [value] (app (function/const* 'data/succ []) value))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- equivalent-transitive [x y z pxy pyz]
  (app (function/const* 'nnrat/equivalent-transitive []) x y z pxy pyz))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))

(def stationary-iterate-fixed-spec
  {:name 'markov/nnrat-stationary-iterate-fixed
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (mass-type 'S)]
     ['mass-stationary (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['target 'S]]
    (req (kernel-iterate 'S 'states 'kernel 'steps 'mass 'target)
         (app 'mass 'target)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (mass-type 'S)]
     ['mass-stationary (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]]
    (let [iterate-at
          (fn [n]
            (function/lam
             [['state 'S]]
             (kernel-iterate 'S 'states 'kernel n 'mass 'state)))
          motive
          (function/lam
           [['n nat]]
           (function/forall
            [['target 'S]]
            (req (kernel-iterate 'S 'states 'kernel 'n 'mass 'target)
                 (app 'mass 'target))))
          base
          (function/lam
           [['target 'S]]
           (equivalent-reflexive (app 'mass 'target)))
          step
          (function/lam
           [['n nat]
            ['previous (app motive 'n)]
            ['target 'S]]
           (equivalent-transitive
            (kernel-iterate 'S 'states 'kernel (succ 'n) 'mass 'target)
            (kernel-step 'S 'states 'kernel (iterate-at 'n) 'target)
            (app 'mass 'target)
            (app (function/const* 'markov/nnrat-kernel-iterate-successor [U])
                 'S 'states 'kernel 'n 'mass 'target)
            (equivalent-transitive
             (kernel-step 'S 'states 'kernel (iterate-at 'n) 'target)
             (kernel-step 'S 'states 'kernel 'mass 'target)
             (app 'mass 'target)
             (app (function/const*
                   'markov/nnrat-kernel-step-respects-mass-equivalence [U])
                  'S 'states 'kernel (iterate-at 'n) 'mass
                  'previous 'target)
             (app 'mass-stationary 'target))))]
      (app (function/const* 'data/Nat.rec [zero-level])
           motive base step 'steps)))})

(def definition-specs [])
(def theorem-specs [stationary-iterate-fixed-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-iteration])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-stationary-iterate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-stationary-iterate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
