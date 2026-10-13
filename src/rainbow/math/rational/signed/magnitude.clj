(ns rainbow.math.rational.signed.magnitude
  "Layer 3 (capstone) of the signed->nnrat magnitude foundation.

    signed/magnitude x := nnrat/monus (positive x) (negative x)   -- a total function
    signed/from-nnrat-magnitude : nonnegative x -> x ~ from-nnrat (magnitude x)

  A nonnegative signed value equals from-nnrat of its magnitude (an nnrat), so the
  magnitude can be reciprocated via the nnrat reciprocal -- the missing lever for the
  limit-product modulus (dividing a radius by |M|, |L|).

  Since signed/nonnegative x reduces to (negative x <= positive x), and signed/equivalent
  x (from-nnrat q) reduces to (positive x + 0) ~ (q + negative x), the property is
  (magnitude x + negative x) ~ positive x [nnrat/monus-add-cancel] chained through
  (positive x + 0) ~ positive x [nnrat/add-zero-right]. Axiom-free; additive."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.monus :as nnrat-monus]
            [rainbow.math.rational.nnrat.identities :as nnrat-identities]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- posp [x] (app (function/const* 'signed/positive []) x))
(defn- negp [x] (app (function/const* 'signed/negative []) x))
(defn- from-nnrat [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nnmonus [p q] (app (function/const* 'nnrat/monus []) p q))
(defn- nnadd [p q] (app (function/const* 'nnrat/add []) p q))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- monus-cancel [p q h] (app (function/const* 'nnrat/monus-add-cancel []) p q h))
(defn- add-zero-right [a] (app (function/const* 'nnrat/add-zero-right []) a))
(defn- eqv-trans [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- eqv-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))

;; signed/magnitude : signed -> nnrat  (total function; = positive x - negative x, truncated)
(def magnitude-spec
  {:name 'signed/magnitude
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['x signed]] (nnmonus (posp 'x) (negp 'x)))})
(defn- magnitude [x] (app (function/const* 'signed/magnitude []) x))

;; nonnegative x -> x ~ from-nnrat (magnitude x)
(def from-nnrat-magnitude-spec
  {:name 'signed/from-nnrat-magnitude
   :universes []
   :type (function/forall [['x signed] ['h (nonneg 'x)]]
                          (sequiv 'x (from-nnrat (magnitude 'x))))
   :value
   (function/lam [['x signed] ['h (nonneg 'x)]]
                 (let [pos (posp 'x) neg (negp 'x)
                       mag (nnmonus pos neg)                    ; = magnitude x (defeq)
           ;; h : nonneg x  defeq  (neg <= pos), feeds monus-add-cancel (p=pos, q=neg)
                       cancel (monus-cancel pos neg 'h)         ; (mag + neg) ~ pos
                       zeroeq (add-zero-right pos)]             ; (pos + 0) ~ pos
       ;; goal reduces to nnrat-equiv (pos + 0) (mag + neg)
                   (eqv-trans (nnadd pos nnzero) pos (nnadd mag neg)
                              zeroeq
                              (eqv-sym (nnadd mag neg) pos cancel))))})

(def theorem-specs [magnitude-spec from-nnrat-magnitude-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.identities])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-magnitude theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.magnitude))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
