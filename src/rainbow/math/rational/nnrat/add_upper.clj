(ns rainbow.math.rational.nnrat.add-upper
  "The additive upper-bound law: a nonnegative rational is at most itself
  plus anything, `a <= a + b`.

  The corpus had the converse cancellation (nnrat/at-most-add-right-cancel)
  but not this direction. It is the shared core of every 'the extra term
  only helps' guarantee -- UCB optimism, expected-improvement's
  exploitation floor, and any acquisition function of the form
  base + nonnegative-bonus -- each of which reduces to one application of
  this lemma. Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.farkas-elim-list :as nnrat-bounds]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- rle [a b] (app (function/const* 'nnrat/at-most []) a b))

(def at-most-add-right-spec
  "a <= a + b, for all nonnegative rationals: a ~ a+0 <= a+b since 0 <= b."
  {:name 'nnrat/at-most-add-right :universes []
   :type (function/forall [['a nnrat] ['b nnrat]] (rle 'a (radd 'a 'b)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [zero-le-b (app (function/const* 'nnrat/zero-at-most []) 'b)
          monotone (app (function/const* 'nnrat/add-left-monotone [])
                        'a nnrat-zero 'b zero-le-b)
          same-left (app (function/const* 'nnrat/equivalent-symmetric [])
                         (radd 'a nnrat-zero) 'a
                         (app (function/const* 'nnrat/add-zero-right []) 'a))]
      (app (function/const* 'nnrat/at-most-respects-equivalence [])
           'a (radd 'a nnrat-zero) (radd 'a 'b) (radd 'a 'b)
           same-left
           (app (function/const* 'nnrat/equivalent-reflexive []) (radd 'a 'b))
           monotone)))})

(def definition-specs [])
(def theorem-specs [at-most-add-right-spec])

(defn- guard [env alias extend]
  (if (environment/resolve-id env alias) env (extend env)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (guard 'nnrat/add-left-monotone add-monotone/extend-environment) (guard 'nnrat/add-zero-right identities/extend-environment) (guard 'nnrat/zero-at-most nnrat-bounds/extend-environment) (support/extend-with :nnrat-add-upper (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.add-upper))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
