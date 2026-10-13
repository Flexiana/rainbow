(ns rainbow.math.linear.matrix.affine-stabilization
  "Exact finite stabilization of signed affine value iteration.

  If two consecutive affine iterates are equivalent, the earlier iterate is a
  certified fixed point.  Iteration composition then proves every later finite
  iterate equivalent to that value and, consequently, every pair of later
  iterates equivalent to each other.  No positivity premise is needed.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-invariant-interval
             :as invariant-interval]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app successor n))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-stable-implies-fixed-point-spec
  {:name 'matrix/affine-iterate-stable-implies-fixed-point :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)]
      (veq (affine 'rows 'offset current) current)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          next (iterate-affine 'rows 'offset (succ 'base) 'initial)
          image (affine 'rows 'offset current)
          successor-unfold
          (app (function/const* 'matrix/affine-iterate-successor [])
               'rows 'offset 'base 'initial)
          image-next
          (equivalent-symmetric next image successor-unfold)
          next-current
          (equivalent-symmetric current next 'stable)]
      (equivalent-transitive
       image next current image-next next-current)))})

(def affine-iterate-stabilizes-spec
  {:name 'matrix/affine-iterate-stabilizes :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]
     ['extra nat]]
    (veq (iterate-affine 'rows 'offset (nadd 'extra 'base) 'initial)
         (iterate-affine 'rows 'offset 'base 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]
     ['extra nat]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          later (iterate-affine 'rows 'offset
                                (nadd 'extra 'base) 'initial)
          nested (iterate-affine 'rows 'offset 'extra current)
          composed
          (app (function/const* 'matrix/affine-iterate-add [])
               'rows 'offset 'initial 'extra 'base)
          fixed
          (app
           (function/const*
            'matrix/affine-iterate-stable-implies-fixed-point [])
           'rows 'offset 'initial 'base 'stable)
          nested-current
          (app (function/const* 'matrix/affine-iterate-fixed-point [])
               'rows 'offset current fixed 'extra)]
      (equivalent-transitive
       later nested current composed nested-current)))})

(def affine-iterate-stable-tail-equivalent-spec
  {:name 'matrix/affine-iterate-stable-tail-equivalent :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]
     ['left-extra nat] ['right-extra nat]]
    (veq (iterate-affine 'rows 'offset
                         (nadd 'left-extra 'base) 'initial)
         (iterate-affine 'rows 'offset
                         (nadd 'right-extra 'base) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]
     ['left-extra nat] ['right-extra nat]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          left-later
          (iterate-affine 'rows 'offset
                          (nadd 'left-extra 'base) 'initial)
          right-later
          (iterate-affine 'rows 'offset
                          (nadd 'right-extra 'base) 'initial)
          left-current
          (app (function/const* 'matrix/affine-iterate-stabilizes [])
               'rows 'offset 'initial 'base 'stable 'left-extra)
          right-current
          (app (function/const* 'matrix/affine-iterate-stabilizes [])
               'rows 'offset 'initial 'base 'stable 'right-extra)
          current-right
          (equivalent-symmetric right-later current right-current)]
      (equivalent-transitive
       left-later current right-later left-current current-right)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-stable-implies-fixed-point-spec
   affine-iterate-stabilizes-spec
   affine-iterate-stable-tail-equivalent-spec])

(defn extend-environment [env]
  (-> env
      invariant-interval/extend-environment
      (support/extend-with :finite-matrix-affine-stabilization theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
