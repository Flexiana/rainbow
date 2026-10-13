(ns rainbow.math.rational.signed.geometric-bridge
  "Bridge exact NNRAT geometry into signed-rational proof data.

  The Grothendieck embedding `signed/from-nnrat` preserves NNRAT equivalence,
  order, and multiplication, and reflects order back: a signed comparison
  between embedded values yields the NNRAT comparison of the originals.  These quotient-safe laws identify the native
  signed half-power recurrence with the existing exact NNRAT sequence
  `nnrat/geometric-half`.  The bridge lets signed vector contraction reuse the
  established harmonic domination and rate-null machinery rather than
  duplicating its arithmetic.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-half-iterate-rate :as rate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.geometric-convergence :as geometric]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.value-iteration :as value-iteration]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-one (function/const* 'signed/one []))
(def signed-half
  (function/app (function/const* 'signed/from-nnrat []) nnrat-half))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- geometric-half [steps]
  (app (function/const* 'nnrat/geometric-half []) steps))

(defn- rat-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- rat-add-respects [left left-prime right right-prime
                         left-same right-same]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def from-nnrat-respects-equivalence-spec
  {:name 'signed/from-nnrat-respects-equivalence :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (veq (from-nnrat 'left) (from-nnrat 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (req 'left 'right)]]
    (rat-add-respects
     'left 'right nnrat-zero nnrat-zero
     'same (rat-reflexive nnrat-zero)))})

(def from-nnrat-at-most-spec
  {:name 'signed/from-nnrat-at-most :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['ordered (rle 'left 'right)]]
    (sle (from-nnrat 'left) (from-nnrat 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['ordered (rle 'left 'right)]]
    (app
     (function/const* 'nnrat/at-most-respects-equivalence [])
     (radd 'left nnrat-zero) 'left
     (radd 'right nnrat-zero) 'right
     (app (function/const* 'nnrat/add-zero-right []) 'left)
     (app (function/const* 'nnrat/add-zero-right []) 'right)
     'ordered))})

(def from-nnrat-at-most-reverse-spec
  {:name 'signed/from-nnrat-at-most-reverse :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['ordered (sle (from-nnrat 'left) (from-nnrat 'right))]]
    (rle 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['ordered (sle (from-nnrat 'left) (from-nnrat 'right))]]
    (app
     (function/const* 'nnrat/at-most-respects-equivalence [])
     'left (radd 'left nnrat-zero)
     'right (radd 'right nnrat-zero)
     (rat-symmetric
      (radd 'left nnrat-zero) 'left
      (app (function/const* 'nnrat/add-zero-right []) 'left))
     (rat-symmetric
      (radd 'right nnrat-zero) 'right
      (app (function/const* 'nnrat/add-zero-right []) 'right))
     'ordered))})

(def from-nnrat-multiply-spec
  {:name 'signed/from-nnrat-multiply :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]]
    (veq
     (smul (from-nnrat 'left) (from-nnrat 'right))
     (from-nnrat (rmul 'left 'right))))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [product (rmul 'left 'right)
          positive
          (radd product (rmul nnrat-zero nnrat-zero))
          negative
          (radd (rmul 'left nnrat-zero)
                (rmul nnrat-zero 'right))
          positive-zero
          (rat-transitive
           positive (radd product nnrat-zero) product
           (rat-add-respects
            product product
            (rmul nnrat-zero nnrat-zero) nnrat-zero
            (rat-reflexive product)
            (app (function/const* 'nnrat/multiply-zero-left [])
                 nnrat-zero))
           (app (function/const* 'nnrat/add-zero-right []) product))
          negative-zero
          (rat-transitive
           negative (radd nnrat-zero nnrat-zero) nnrat-zero
           (rat-add-respects
            (rmul 'left nnrat-zero) nnrat-zero
            (rmul nnrat-zero 'right) nnrat-zero
            (app (function/const* 'nnrat/multiply-zero-right [])
                 'left)
            (app (function/const* 'nnrat/multiply-zero-left [])
                 'right))
           (app (function/const* 'nnrat/add-zero-right [])
                nnrat-zero))
          source (radd positive nnrat-zero)
          middle (radd product nnrat-zero)
          target (radd product negative)
          source-middle
          (rat-add-respects
           positive product nnrat-zero nnrat-zero
           positive-zero (rat-reflexive nnrat-zero))
          target-middle
          (rat-add-respects
           product product negative nnrat-zero
           (rat-reflexive product) negative-zero)]
      (rat-transitive
       source middle target
       source-middle
       (rat-symmetric target middle target-middle))))})

(def half-power-one-geometric-spec
  {:name 'signed/half-power-one-geometric :universes []
   :type
   (function/forall
    [['steps nat]]
    (veq (half-power-scale 'steps signed-one)
         (from-nnrat (geometric-half 'steps))))
   :value
   (function/lam
    [['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (veq (half-power-scale 'n signed-one)
                (from-nnrat (geometric-half 'n))))
          step
          (function/lam
           [['n nat] ['previous-geometric (app motive 'n)]]
           (let [previous (half-power-scale 'n signed-one)
                 geometric (geometric-half 'n)
                 next-geometric (geometric-half (succ 'n))
                 scaled-previous (smul signed-half previous)
                 scaled-geometric
                 (smul signed-half (from-nnrat geometric))
                 embedded-product
                 (from-nnrat (rmul nnrat-half geometric))]
             (signed-transitive
              scaled-previous scaled-geometric
              (from-nnrat next-geometric)
              (app
               (function/const*
                'signed/multiply-left-respects-equivalence [])
               previous (from-nnrat geometric) signed-half
               'previous-geometric)
              (signed-transitive
               scaled-geometric embedded-product
               (from-nnrat next-geometric)
               (app (function/const* 'signed/from-nnrat-multiply [])
                    nnrat-half geometric)
               (app
                (function/const*
                 'signed/from-nnrat-respects-equivalence [])
                (rmul nnrat-half geometric) next-geometric
                (app
                 (function/const* 'nnrat/geometric-half-halving [])
                 'n))))))]
      (prop-nat-rec
       motive
       (app (function/const* 'signed/equivalent-reflexive [])
            signed-one)
       step 'steps)))})

(def definition-specs [])
(def theorem-specs
  [from-nnrat-respects-equivalence-spec
   from-nnrat-at-most-spec
   from-nnrat-at-most-reverse-spec
   from-nnrat-multiply-spec
   half-power-one-geometric-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-half-iterate-rate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/multiply-zero-right :nnrat-identities identities/multiply-zero-right-spec) (extend-spec-if-missing 'nnrat/multiply-zero-left :nnrat-identities identities/multiply-zero-left-spec) (extend-spec-if-missing 'nat/pow2-pred :nnrat-geometric-convergence geometric/pow2-pred-spec) (extend-spec-if-missing 'nnrat/geometric-half :nnrat-geometric-convergence geometric/geometric-spec) (extend-spec-if-missing 'nat/two-times :nnrat-value-iteration value-iteration/two-times-spec) (extend-spec-if-missing 'nat/two-times-succ :nnrat-value-iteration value-iteration/two-times-succ-spec) (extend-spec-if-missing 'nnrat/geometric-half-halving :nnrat-value-iteration value-iteration/geom-halving-spec) (support/extend-with :signed-geometric-bridge theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.geometric-bridge))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
