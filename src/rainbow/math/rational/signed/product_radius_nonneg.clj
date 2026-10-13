(ns rainbow.math.rational.signed.product-radius-nonneg
  "First sub-proof of the limit-product modulus assembly: the radius base
  V = (1 + |L|) + |M| is nonnegative (indeed a sum of nonnegatives), so
  signed/from-nnrat-magnitude applies to it. Axiom-free; additive.

  analysis/product-radius-nonneg :
    forall L M, signed/nonnegative (signed-add (signed-add one (absolute L)) (absolute M))"
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute :as absolute]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private one (function/const* 'signed/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- add-nn [a b ha hb] (app (function/const* 'signed/add-nonnegative []) a b ha hb))
(defn- nn-of-le [w h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) w h))
(defn- abs-nn [x] (app (function/const* 'signed/absolute-nonnegative []) x))
(def ^:private zero-le-one (function/const* 'signed/zero-at-most-one []))

(def product-radius-nonneg-spec
  {:name 'analysis/product-radius-nonneg
   :universes []
   :type (function/forall [['L signed] ['M signed]]
                          (nonneg (sadd (sadd one (abs* 'L)) (abs* 'M))))
   :value
   (function/lam [['L signed] ['M signed]]
                 (let [nn-one (nn-of-le one zero-le-one)              ; nonnegative one
                       nn-absL (nn-of-le (abs* 'L) (abs-nn 'L))       ; nonnegative |L|
                       nn-B (add-nn one (abs* 'L) nn-one nn-absL)     ; nonnegative (1 + |L|)
                       nn-absM (nn-of-le (abs* 'M) (abs-nn 'M))]      ; nonnegative |M|
                   (add-nn (sadd one (abs* 'L)) (abs* 'M) nn-B nn-absM)))})

(def theorem-specs [product-radius-nonneg-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.absolute rainbow.math.rational.signed.unit-laws rainbow.math.linear.vector.norm-nonnegative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-product-radius-nonneg theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.product-radius-nonneg))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
