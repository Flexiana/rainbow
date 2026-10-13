(ns rainbow.math.linear.matrix.affine-residual-bracket
  "Nested finite-horizon affine brackets from linear residual certificates.

  A lower residual upper-bound and upper residual lower-bound, together with
  nonnegative rows and an initial lower/upper order, produce the full nested
  certificate `L_base <= L_(extra+base) <= U_(extra+base) <= U_base`.
  This is the exact finite bounded-value-iteration enclosure used to tighten
  lower and upper Bellman certificates.  Theorem-only, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual-iteration
             :as residual-iteration]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def affine-iterate-residual-nested-bracket-spec
  {:name 'matrix/affine-iterate-residual-nested-bracket :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat] ['extra nat]]
    (let [later (nadd 'extra 'base)
          lower-base (iterate-affine 'rows 'offset 'base 'lower)
          lower-later (iterate-affine 'rows 'offset later 'lower)
          upper-later (iterate-affine 'rows 'offset later 'upper)
          upper-base (iterate-affine 'rows 'offset 'base 'upper)]
      (both
       (vle lower-base lower-later)
       (both (vle lower-later upper-later)
             (vle upper-later upper-base)))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat] ['extra nat]]
    (let [later (nadd 'extra 'base)
          lower-base (iterate-affine 'rows 'offset 'base 'lower)
          lower-later (iterate-affine 'rows 'offset later 'lower)
          upper-later (iterate-affine 'rows 'offset later 'upper)
          upper-base (iterate-affine 'rows 'offset 'base 'upper)
          lower-subsolution
          (app
           (function/const*
            'matrix/affine-residual-upper-bound-implies-subsolution [])
           'rows 'offset 'lower 'lower-image-shape
           'lower-residual-upper)
          upper-supersolution
          (app
           (function/const*
            'matrix/affine-residual-lower-bound-implies-supersolution [])
           'rows 'offset 'upper 'upper-image-shape
           'upper-residual-lower)
          lower-grows
          (app
           (function/const* 'matrix/affine-iterate-subsolution-horizon [])
           'rows 'offset 'lower 'rows-positive lower-subsolution
           'base 'extra)
          later-ordered
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'lower 'upper
               'rows-positive 'lower-upper later)
          upper-shrinks
          (app
           (function/const* 'matrix/affine-iterate-supersolution-horizon [])
           'rows 'offset 'upper 'rows-positive upper-supersolution
           'base 'extra)
          inner
          (conjoin
           (vle lower-later upper-later)
           (vle upper-later upper-base)
           later-ordered upper-shrinks)]
      (conjoin
       (vle lower-base lower-later)
       (both (vle lower-later upper-later)
             (vle upper-later upper-base))
       lower-grows inner)))})

(def definition-specs [])
(def theorem-specs [affine-iterate-residual-nested-bracket-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-iteration])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-residual-bracket theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-residual-bracket))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
