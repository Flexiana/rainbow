(ns rainbow.math.rational.nnrat.half-positive
  "nnrat/half-positive : 0 < half (as the reducible conjunction 0<=half AND not(0~half)).
  half ~ 0 unfolds (defeq) to equality Nat (succ zero) zero (num(half)*den(0) reduces to succ zero,
  num(0)*den(half) to zero), so it is refuted exactly like nnrat/one-not-equivalent-zero -- no
  multiply lemmas needed, keeping the dependency chain minimal (farkas only, for zero-at-most).
  Provides the positive symmetric weight for strict-convexity minimizer uniqueness."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private nnzero (function/const* 'nnrat/zero []))
(def ^:private half (function/const* 'nnrat/half []))
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- eqv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nle [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- esym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- zero-at-most [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(defn- pconj [l r] (app (function/const* 'proposition/conjunction []) l r))
(defn- conjoin [l r hl hr] (app (function/const* 'proposition/conjoin []) l r hl hr))
(defn- zero-not-succ [v] (app (function/const* 'nat/zero-not-successor []) v))
(defn- eq-symm [u A a b h] (app (function/const* 'equality/symmetric [u]) A a b h))

;; 0 < half  ==  conjunction (0 <= half) (not (0 ~ half)).
(def half-positive-spec
  {:name 'nnrat/half-positive
   :universes []
   :type (pconj (nle nnzero half) (pneg (eqv nnzero half)))
   :value
   (conjoin (nle nnzero half) (pneg (eqv nnzero half))
            (zero-at-most half)                                     ; 0 <= half
            (function/lam [['h (eqv nnzero half)]]                  ; not(0 ~ half)
              ;; (esym) half ~ 0  :defeq  equality Nat (succ zero) zero; flip + discriminate.
                          (app (zero-not-succ nat-zero)
                               (eq-symm [:succ [:zero]] nat (succ nat-zero) nat-zero
                                        (esym nnzero half 'h)))))})

(def theorem-specs [half-positive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      farkas/extend-environment
      (support/extend-with :nnrat-half-positive theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
