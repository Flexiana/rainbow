(ns rainbow.math.linear.vector.norm-parallelogram
  "The exact parallelogram identity for native signed vectors.

    signed/parallelogram-recombine
    norm/norm-squared-parallelogram

  The scalar lemma cancels the two cross terms in the addition and subtraction
  expansions as a Grothendieck-pair semiring identity.  Substituting the native
  squared-norm expansions yields

      ||a+b||^2 + ||a-b||^2  ~  (||a||^2+||a||^2) + (||b||^2+||b||^2)

  for same-shaped vectors, without division, square roots, or axioms."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.linear.vector.norm-expansion :as expansion]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def parallelogram-recombine-spec
  {:name 'signed/parallelogram-recombine :universes []
   :type
   (function/forall
    [['a signed] ['b signed] ['c signed] ['d signed]]
    (signed-equivalent
     (signed-add
      (signed-add (signed-add 'a 'b) (signed-add 'c 'd))
      (signed-subtract
       (signed-subtract 'a 'b)
       (signed-subtract 'c 'd)))
     (signed-add
      (signed-add 'a 'a)
      (signed-add 'd 'd))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed] ['d signed]]
    (let [pa (positive 'a) na (negative 'a)
          pb (positive 'b) nb (negative 'b)
          pc (positive 'c) nc (negative 'c)
          pd (positive 'd) nd (negative 'd)
          sum-positive
          (ring/radd (ring/radd pa pb) (ring/radd pc pd))
          sum-negative
          (ring/radd (ring/radd na nb) (ring/radd nc nd))
          difference-positive
          (ring/radd (ring/radd pa nb) (ring/radd nc pd))
          difference-negative
          (ring/radd (ring/radd na pb) (ring/radd pc nd))
          left-positive (ring/radd sum-positive difference-positive)
          left-negative (ring/radd sum-negative difference-negative)
          right-positive
          (ring/radd (ring/radd pa pa) (ring/radd pd pd))
          right-negative
          (ring/radd (ring/radd na na) (ring/radd nd nd))]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def norm-squared-parallelogram-spec
  {:name 'norm/norm-squared-parallelogram :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (signed-add
      (norm-squared (vector-add 'left 'right))
      (norm-squared (vector-subtract 'left 'right)))
     (signed-add
      (signed-add (norm-squared 'left) (norm-squared 'left))
      (signed-add (norm-squared 'right) (norm-squared 'right)))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [left-square (norm-squared 'left)
          right-square (norm-squared 'right)
          left-right (dot 'left 'right)
          right-left (dot 'right 'left)
          expanded-add
          (signed-add
           (signed-add left-square left-right)
           (signed-add right-left right-square))
          expanded-subtract
          (signed-subtract
           (signed-subtract left-square left-right)
           (signed-subtract right-left right-square))
          start
          (signed-add
           (norm-squared (vector-add 'left 'right))
           (norm-squared (vector-subtract 'left 'right)))
          expanded (signed-add expanded-add expanded-subtract)
          finish
          (signed-add
           (signed-add left-square left-square)
           (signed-add right-square right-square))
          expand-both
          (app (function/const* 'signed/add-respects-equivalence [])
               (norm-squared (vector-add 'left 'right)) expanded-add
               (norm-squared (vector-subtract 'left 'right))
               expanded-subtract
               (app (function/const* 'norm/norm-squared-add [])
                    'left 'right 'same)
               (app (function/const* 'norm/norm-squared-subtract [])
                    'left 'right 'same))]
      (transitive
       start expanded finish
       expand-both
       (app (function/const* 'signed/parallelogram-recombine [])
            left-square left-right right-left right-square))))})

(def definition-specs [])
(def theorem-specs
  [parallelogram-recombine-spec norm-squared-parallelogram-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.norm-expansion])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-norm-parallelogram theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.norm-parallelogram))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
