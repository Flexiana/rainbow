(ns rainbow.math.linear.matrix.affine-half-iterate-rate
  "Finite-horizon geometric rate for half-row signed affine iteration.

  `signed/half-power-scale n d` is the native recurrence d, (1/2)d,
  (1/2)((1/2)d), ... .  Its zero/successor equations, nonnegativity, and
  monotonicity are proof data.  Induction over the one-step affine contraction
  then gives the explicit all-horizon bound

      sup-distance(F^n x, F^n y) <= half-power-scale n (sup-distance x y).

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-half-iterate-contraction
             :as contraction]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-half
  (function/app
   (function/const* 'signed/from-nnrat [])
   (function/const* 'nnrat/half [])))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [type-level])
       motive base step value))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- half-row-sums [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) signed-half)))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))

(def half-power-scale-spec
  {:name 'signed/half-power-scale :kind :definition :universes []
   :type (function/arrow nat signed signed)
   :value
   (function/lam
    [['steps nat] ['value signed]]
    (nat-rec
     (function/lam [['ignored nat]] signed)
     'value
     (function/lam
      [['ignored-step nat] ['previous signed]]
      (smul signed-half 'previous))
     'steps))})

(def half-power-scale-zero-spec
  {:name 'signed/half-power-scale-zero :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (half-power-scale nat-zero 'value) 'value))
   :value
   (function/lam
    [['value signed]]
    (app (function/const* 'signed/equivalent-reflexive []) 'value))})

(def half-power-scale-successor-spec
  {:name 'signed/half-power-scale-successor :universes []
   :type
   (function/forall
    [['steps nat] ['value signed]]
    (veq (half-power-scale (succ 'steps) 'value)
         (smul signed-half (half-power-scale 'steps 'value))))
   :value
   (function/lam
    [['steps nat] ['value signed]]
    (app
     (function/const* 'signed/equivalent-reflexive [])
     (smul signed-half (half-power-scale 'steps 'value))))})

(def half-power-scale-nonnegative-spec
  {:name 'signed/half-power-scale-nonnegative :universes []
   :type
   (function/forall
    [['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (sle signed-zero (half-power-scale 'steps 'value)))
   :value
   (function/lam
    [['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (sle signed-zero (half-power-scale 'n 'value)))
          step
          (function/lam
           [['n nat] ['previous-nonnegative (app motive 'n)]]
           (let [previous (half-power-scale 'n 'value)
                 product (smul signed-half previous)]
             (app
              (function/const* 'signed/zero-at-most-of-nonnegative [])
              product
              (app
               (function/const* 'signed/multiply-nonnegative [])
               signed-half previous
               (app
                (function/const* 'signed/nonnegative-of-zero-at-most [])
                signed-half
                (function/const* 'signed/zero-at-most-half []))
               (app
                (function/const* 'signed/nonnegative-of-zero-at-most [])
                previous 'previous-nonnegative)))))]
      (prop-nat-rec motive 'value-nonnegative step 'steps)))})

(def half-power-scale-monotone-spec
  {:name 'signed/half-power-scale-monotone :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['ordered (sle 'left 'right)] ['steps nat]]
    (sle (half-power-scale 'steps 'left)
         (half-power-scale 'steps 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['ordered (sle 'left 'right)] ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (sle (half-power-scale 'n 'left)
                (half-power-scale 'n 'right)))
          step
          (function/lam
           [['n nat] ['previous-ordered (app motive 'n)]]
           (app
            (function/const* 'signed/multiply-left-monotone [])
            signed-half
            (half-power-scale 'n 'left)
            (half-power-scale 'n 'right)
            (function/const* 'signed/zero-at-most-half [])
            'previous-ordered))]
      (prop-nat-rec motive 'ordered step 'steps)))})

(def affine-half-iterate-sup-distance-rate-spec
  {:name 'matrix/affine-half-iterate-sup-distance-rate :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (half-row-sums 'rows)]
     ['steps nat]]
    (sle
     (sup-distance
      (affine-iterate 'rows 'offset 'steps 'left)
      (affine-iterate 'rows 'offset 'steps 'right))
     (half-power-scale 'steps (sup-distance 'left 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (half-row-sums 'rows)]
     ['steps nat]]
    (let [distance-at
          (fn [n]
            (sup-distance
             (affine-iterate 'rows 'offset n 'left)
             (affine-iterate 'rows 'offset n 'right)))
          initial-distance (sup-distance 'left 'right)
          motive
          (function/lam
           [['n nat]]
           (sle (distance-at 'n)
                (half-power-scale 'n initial-distance)))
          step
          (function/lam
           [['n nat] ['previous-bound (app motive 'n)]]
           (let [previous-distance (distance-at 'n)
                 previous-envelope
                 (half-power-scale 'n initial-distance)
                 next-envelope
                 (smul signed-half previous-envelope)
                 one-step
                 (app
                  (function/const*
                   'matrix/affine-half-iterate-sup-distance-step [])
                  'rows 'offset 'left 'right
                  'initial-shape 'offset-shape
                  'positive-rows 'bounded-sums 'n)
                 scaled-bound
                 (app
                  (function/const* 'signed/multiply-left-monotone [])
                  signed-half previous-distance previous-envelope
                  (function/const* 'signed/zero-at-most-half [])
                  'previous-bound)]
             (order-transitive
              (distance-at (succ 'n))
              (smul signed-half previous-distance)
              next-envelope
              one-step scaled-bound)))]
      (prop-nat-rec
       motive
       (app (function/const* 'signed/at-most-reflexive [])
            initial-distance)
       step 'steps)))})

(def definition-specs [half-power-scale-spec])
(def theorem-specs
  [half-power-scale-zero-spec
   half-power-scale-successor-spec
   half-power-scale-nonnegative-spec
   half-power-scale-monotone-spec
   affine-half-iterate-sup-distance-rate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-half-iterate-contraction])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-half-iterate-rate (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-half-iterate-rate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
