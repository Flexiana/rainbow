(ns rainbow.math.logic.clamp-range
  "Universal correctness of clamping (the PPO / trust-region clip of AHoF D52), built on
  the general nnrat min/max bounds:

      clamp r lo hi = min (max r lo) hi

  Proved for ALL r, lo, hi (not just worked instances):
    clamp-at-most-hi : clamp r lo hi <= hi
    lo-at-most-clamp : lo <= hi -> lo <= clamp r lo hi

  Together: whenever lo <= hi, the clamped value provably lies in the interval
  [lo, hi] for every input r -- the guarantee the clip step relies on. Native and
  axiom-free; chains rainbow.math.rational.nnrat.minmax."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- minimum [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- maximum [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- clamp [r lo hi] (function/app (function/const* 'clamp/clamp []) r lo hi))

;; clamp r lo hi = min (max r lo) hi
(def clamp-spec
  {:name 'clamp/clamp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['r nnrat] ['lo nnrat] ['hi nnrat]]
                        (minimum (maximum 'r 'lo) 'hi))})

(def definition-specs [clamp-spec])

;; clamp r lo hi <= hi   (from min-lower-right on (max r lo) and hi)
(def clamp-at-most-hi-spec
  {:name 'clamp/clamp-at-most-hi :universes []
   :type (function/forall [['r nnrat] ['lo nnrat] ['hi nnrat]]
                          (at-most (clamp 'r 'lo 'hi) 'hi))
   :value (function/lam
           [['r nnrat] ['lo nnrat] ['hi nnrat]]
           (function/app (function/const* 'minmax/min-lower-right [])
                         (maximum 'r 'lo) 'hi))})

;; lo <= hi -> lo <= clamp r lo hi
;; clamp = min (max r lo) hi ; at-most-min lo (max r lo) hi needs lo<=max r lo and lo<=hi
(def lo-at-most-clamp-spec
  {:name 'clamp/lo-at-most-clamp :universes []
   :type (function/forall
          [['r nnrat] ['lo nnrat] ['hi nnrat]
           ['ordered (at-most 'lo 'hi)]]
          (at-most 'lo (clamp 'r 'lo 'hi)))
   :value (function/lam
           [['r nnrat] ['lo nnrat] ['hi nnrat]
            ['ordered (at-most 'lo 'hi)]]
           (function/app
            (function/const* 'minmax/at-most-min [])
            'lo (maximum 'r 'lo) 'hi
            (function/app (function/const* 'minmax/max-upper-right []) 'r 'lo)
            'ordered))})

(def theorem-specs [clamp-at-most-hi-spec lo-at-most-clamp-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :clamp-range (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.logic.clamp-range))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
