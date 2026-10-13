(ns rainbow.math.rational.signed.indexed-max
  "Index-aware MAX aggregation -- the argmax semantic core, continuing the non-invasive Level-6 line
  (indexed-sum -> indexed-max). Reads env at each index and folds signed/max from a fallback init.
     signed/indexed-max-from env init n := max(init, env 0, ..., env (n-1))   (Nat.rec)
     signed/indexed-max-from-dominates-init : forall env init n, init <= indexed-max-from env init n
     signed/indexed-max-from-upper-of-last  : forall env init m, env m <= indexed-max-from env init (succ m)
  The dominance-of-init is proved by induction (max-upper-left + at-most-transitive); the last-element
  bound is direct (max-upper-right). The full 'dominates every index below n' is a follow-on needing
  strict-below case analysis. This is the semantic target a future index-aware fold CONSTRUCTOR would
  let a verified program compute -- see the design notes."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.order-transitivity :as order-trans]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private environment-type (function/arrow nat signed))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- at-most-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- at-most-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- max-upper-left [a b] (app (function/const* 'signed/max-upper-left []) a b))
(defn- max-upper-right [a b] (app (function/const* 'signed/max-upper-right []) a b))

;; indexed-max-from env init n = max(init, env 0, ..., env (n-1)); reads env at each index.
(def indexed-max-from-spec
  {:name 'signed/indexed-max-from
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow environment-type (function/arrow signed (function/arrow nat signed)))
   :value (function/lam
           [['env environment-type] ['init signed] ['n nat]]
           (app (function/const* 'data/Nat.rec [type-level])
                (function/lam [['ignored nat]] signed)
                'init
                (function/lam [['pred nat] ['rec signed]] (smax 'rec (app 'env 'pred)))
                'n))})

(defn- imax [env init n] (app (function/const* 'signed/indexed-max-from []) env init n))

(def dominates-init-spec
  {:name 'signed/indexed-max-from-dominates-init
   :universes []
   :type (function/forall
          [['env environment-type] ['init signed] ['n nat]]
          (sle 'init (imax 'env 'init 'n)))
   :value
   (let [im (fn [k] (imax 'env 'init k))
         motive (function/lam [['k nat]] (sle 'init (im 'k)))
         base (at-most-refl 'init)                              ; init <= im 0 (=defeq init)
         stepfn (function/lam
                 [['m nat] ['ih (sle 'init (im 'm))]]
                 ;; im (succ m) =defeq= max (im m) (env m); init <= im m <= max (im m)(env m)
                 (at-most-trans 'init (im 'm) (im (succ 'm))
                                'ih
                                (max-upper-left (im 'm) (app 'env 'm))))]
     (function/lam
      [['env environment-type] ['init signed] ['n nat]]
      (app (function/app (function/const* 'data/Nat.rec [prop-level]) motive base stepfn) 'n)))})

(def upper-of-last-spec
  {:name 'signed/indexed-max-from-upper-of-last
   :universes []
   :type (function/forall
          [['env environment-type] ['init signed] ['m nat]]
          (sle (app 'env 'm) (imax 'env 'init (succ 'm))))
   :value (function/lam
           [['env environment-type] ['init signed] ['m nat]]
           ;; imax env init (succ m) =defeq= max (imax env init m) (env m)
           (max-upper-right (imax 'env 'init 'm) (app 'env 'm)))})

(def theorem-specs [indexed-max-from-spec dominates-init-spec upper-of-last-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.minmax rainbow.math.rational.signed.order-transitivity])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-indexed-max theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.indexed-max))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
