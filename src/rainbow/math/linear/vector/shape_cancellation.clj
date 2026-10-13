(ns rainbow.math.linear.vector.shape-cancellation
  "Shape equality and sound cancellation for truncating vector arithmetic.

  Native vector/add truncates to the shorter list, so cancellation is false
  without a dimension hypothesis.  vector/same-shape compares the corresponding
  zero-like vectors and therefore records equal dimension without inspecting
  components.  Under that hypothesis both right-cancellation orientations hold:

    (left - right) + right  ~  left
    (left + right) - right  ~  left

  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.additive-units :as units]
            [rainbow.math.linear.vector.equivalence-laws :as equivalence-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))

(def same-shape-spec
  {:name 'vector/same-shape :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type 'Prop)
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (vector-equivalent (zero-like 'left) (zero-like 'right)))})

(def same-shape-reflexive-spec
  {:name 'vector/same-shape-reflexive :universes []
   :type
   (function/forall
    [['values vector-type]]
    (same-shape 'values 'values))
   :value
   (function/lam
    [['values vector-type]]
    (app (function/const* 'vector/equivalent-reflexive [])
         (zero-like 'values)))})

(def same-shape-symmetric-spec
  {:name 'vector/same-shape-symmetric :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (same-shape 'right 'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (app (function/const* 'vector/equivalent-symmetric [])
         (zero-like 'left) (zero-like 'right) 'same))})

(def same-shape-transitive-spec
  {:name 'vector/same-shape-transitive :universes []
   :type
   (function/forall
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (same-shape 'left 'middle)]
     ['middle-right (same-shape 'middle 'right)]]
    (same-shape 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (same-shape 'left 'middle)]
     ['middle-right (same-shape 'middle 'right)]]
    (app (function/const* 'vector/equivalent-transitive [])
         (zero-like 'left) (zero-like 'middle) (zero-like 'right)
         'left-middle 'middle-right))})

(defn- cancel-chain
  [left right same-shape-evidence first-step inverse-step start inner]
  (let [associated (vector-add left inner)
        with-right-zero (vector-add left (zero-like right))
        with-left-zero (vector-add left (zero-like left))
        finish left
        left-reflexive
        (app (function/const* 'vector/equivalent-reflexive []) left)
        replace-inverse
        (app (function/const* 'vector/add-respects-equivalence [])
             left left
             inner (zero-like right)
             left-reflexive inverse-step)
        reverse-shape
        (app (function/const* 'vector/equivalent-symmetric [])
             (zero-like left) (zero-like right) same-shape-evidence)
        align-zero
        (app (function/const* 'vector/add-respects-equivalence [])
             left left
             (zero-like right) (zero-like left)
             left-reflexive reverse-shape)
        remove-zero
        (app (function/const* 'vector/add-zero-like-right []) left)]
    (app
     (function/const* 'vector/equivalent-transitive [])
     start with-left-zero finish
     (app
      (function/const* 'vector/equivalent-transitive [])
      start with-right-zero with-left-zero
      (app
       (function/const* 'vector/equivalent-transitive [])
       start associated with-right-zero
       first-step replace-inverse)
      align-zero)
     remove-zero)))

(def subtract-add-right-cancel-spec
  {:name 'vector/subtract-add-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (vector-equivalent
     (vector-add (vector-subtract 'left 'right) 'right)
     'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [start
          (vector-add (vector-subtract 'left 'right) 'right)
          inner (vector-add (vector-negate 'right) 'right)]
      (cancel-chain
       'left 'right 'same
       (app (function/const* 'vector/add-associative [])
            'left (vector-negate 'right) 'right)
       (app
        (function/const* 'vector/add-negate-left-equivalent-zero-like [])
        'right)
       start inner)))})

(def add-subtract-right-cancel-spec
  {:name 'vector/add-subtract-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (vector-equivalent
     (vector-subtract (vector-add 'left 'right) 'right)
     'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [start
          (vector-subtract (vector-add 'left 'right) 'right)
          inner (vector-add 'right (vector-negate 'right))]
      (cancel-chain
       'left 'right 'same
       (app (function/const* 'vector/add-associative [])
            'left 'right (vector-negate 'right))
       (app
        (function/const* 'vector/add-negate-right-equivalent-zero-like [])
        'right)
       start inner)))})

(def definition-specs [same-shape-spec])
(def theorem-specs
  [same-shape-reflexive-spec
   same-shape-symmetric-spec
   same-shape-transitive-spec
   subtract-add-right-cancel-spec
   add-subtract-right-cancel-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.additive-units])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'vector/equivalent-reflexive :vector-equivalence-laws equivalence-laws/equivalent-reflexive-spec) (extend-spec-if-missing 'vector/equivalent-symmetric :vector-equivalence-laws equivalence-laws/equivalent-symmetric-spec) (support/extend-with :vector-shape-cancellation (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.shape-cancellation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
