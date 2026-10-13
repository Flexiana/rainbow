(ns rainbow.math.rational.nnrat.lp-separable-two-var
  "Strong duality for the sum of two decoupled scalar nnrat LPs.

  Each coordinate uses the canonical witnesses x_i=b_i/a_i and y_i=c_i/a_i
  from lp-single-positive-constraint-strong-duality.  Adding the two scalar
  zero-gap equivalences proves equality of the summed objectives."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.lp-strong-duality-general :as general]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))
(def upper-family
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat list-nnrat))
(def layer
  (function/app (function/const* 'data/Product [type-level type-level])
                list-nnrat upper-family))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- positive [numerator-predecessor denominator-predecessor]
  (make (succ numerator-predecessor) denominator-predecessor))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- nil-of [carrier]
  (function/app (function/const* 'data/nil [type-level]) carrier))
(defn- cons-of [carrier head tail]
  (function/app (function/const* 'data/cons [type-level])
                carrier head tail))

(defn- primal-feasible [a b x]
  (at-most (multiply a x) b))
(defn- dual-feasible [a c y]
  (at-most c (multiply a y)))
(defn- gap [b c x y]
  (equivalent (multiply c x) (multiply b y)))
(defn- primal-optimal [a b c x]
  (function/forall
   [['x-alt nnrat] ['hp-alt (primal-feasible a b 'x-alt)]]
   (at-most (multiply c 'x-alt) (multiply c x))))
(defn- dual-optimal [a b c y]
  (function/forall
   [['y-alt nnrat] ['hd-alt (dual-feasible a c 'y-alt)]]
   (at-most (multiply b y) (multiply b 'y-alt))))
(defn- matching-system [a b c x]
  (let [nil-nnrat (nil-of nnrat)
        nil-layer (nil-of layer)
        lower (divide c a)
        upper (divide (multiply c x) b)
        lowers (cons-of nnrat lower nil-nnrat)]
    (function/app
     (function/const* 'nnrat/farkas-elim-chain-solvable [])
     nil-layer lowers upper nil-nnrat)))
(defn- scalar-bundle [a b c x y]
  (proposition/conjunction
   (primal-feasible a b x)
   (proposition/conjunction
    (dual-feasible a c y)
    (proposition/conjunction
     (gap b c x y)
     (proposition/conjunction
      (primal-optimal a b c x)
      (proposition/conjunction
       (dual-optimal a b c y)
       (matching-system a b c x)))))))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- add-respects [left left-equivalent right right-equivalent
                     same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-equivalent right right-equivalent
                same-left same-right))

(defn- scalar-gap [a b c x y bundle]
  (let [hp (primal-feasible a b x)
        hd (dual-feasible a c y)
        hgap (gap b c x y)
        primal-best (primal-optimal a b c x)
        dual-best (dual-optimal a b c y)
        system (matching-system a b c x)
        optimal-tail
        (proposition/conjunction
         primal-best (proposition/conjunction dual-best system))
        gap-tail (proposition/conjunction hgap optimal-tail)
        dual-tail (proposition/conjunction hd gap-tail)]
    (left-conjunct
     hgap optimal-tail
     (right-conjunct
      hd gap-tail
      (right-conjunct hp dual-tail bundle)))))

(def separable-two-var-zero-gap-spec
  {:name 'nnrat/lp-separable-two-var-zero-gap
   :universes []
   :type
   (function/forall
    [['a1p nat] ['a1dp nat] ['b1p nat] ['b1dp nat] ['c1 nnrat]
     ['a2p nat] ['a2dp nat] ['b2p nat] ['b2dp nat] ['c2 nnrat]]
    (let [a1 (positive 'a1p 'a1dp)
          b1 (positive 'b1p 'b1dp)
          x1 (divide b1 a1)
          y1 (divide 'c1 a1)
          a2 (positive 'a2p 'a2dp)
          b2 (positive 'b2p 'b2dp)
          x2 (divide b2 a2)
          y2 (divide 'c2 a2)]
      (equivalent
       (add (multiply 'c1 x1) (multiply 'c2 x2))
       (add (multiply b1 y1) (multiply b2 y2)))))
   :value
   (function/lam
    [['a1p nat] ['a1dp nat] ['b1p nat] ['b1dp nat] ['c1 nnrat]
     ['a2p nat] ['a2dp nat] ['b2p nat] ['b2dp nat] ['c2 nnrat]]
    (let [a1 (positive 'a1p 'a1dp)
          b1 (positive 'b1p 'b1dp)
          x1 (divide b1 a1)
          y1 (divide 'c1 a1)
          a2 (positive 'a2p 'a2dp)
          b2 (positive 'b2p 'b2dp)
          x2 (divide b2 a2)
          y2 (divide 'c2 a2)
          single1
          (function/app
           (function/const*
            'nnrat/lp-single-positive-constraint-strong-duality [])
           'a1p 'a1dp 'b1p 'b1dp 'c1)
          single2
          (function/app
           (function/const*
            'nnrat/lp-single-positive-constraint-strong-duality [])
           'a2p 'a2dp 'b2p 'b2dp 'c2)
          gap1 (scalar-gap a1 b1 'c1 x1 y1 single1)
          gap2 (scalar-gap a2 b2 'c2 x2 y2 single2)]
      (add-respects
       (multiply 'c1 x1) (multiply b1 y1)
       (multiply 'c2 x2) (multiply b2 y2)
       gap1 gap2)))})

(def definition-specs [])
(def theorem-specs [separable-two-var-zero-gap-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      general/extend-environment
      (support/extend-with :nnrat-lp-separable-two-var theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
