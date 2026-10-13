(ns rainbow.math.rational.nnrat.additive-reassociation
  "Associativity and reusable summand reorder laws for native nonnegative
  rationals.  The foundational associativity proof unfolds rational addition to
  its numerator/positive-denominator cross product and asks the verified nat
  semiring normalizer for a kernel-checkable equality proof.  The two downstream
  laws are then assembled from associativity, commutativity, congruence, symmetry,
  and transitivity at the nnrat equivalence layer."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))

(defn- equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))

(defn- add-respects [left left-equivalent right right-equivalent
                     same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-equivalent right right-equivalent
                same-left same-right))

(defn- add-commutative [left right]
  (function/app (function/const* 'nnrat/add-commutative []) left right))

;; ((a+b)+c) ~ (a+(b+c)).  After unfolding, both sides of the cross-product
;; equality are the same coefficient-free nat polynomial.
(def add-associative-spec
  {:name 'nnrat/add-associative
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (equivalent (add (add 'a 'b) 'c)
                (add 'a (add 'b 'c))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (let [na (numerator 'a)
          nb (numerator 'b)
          nc (numerator 'c)
          da (denominator 'a)
          db (denominator 'b)
          dc (denominator 'c)
          numerator-ab (ring/nadd (ring/nmul na db) (ring/nmul nb da))
          denominator-ab (ring/nmul da db)
          numerator-bc (ring/nadd (ring/nmul nb dc) (ring/nmul nc db))
          denominator-bc (ring/nmul db dc)
          left-numerator
          (ring/nadd (ring/nmul numerator-ab dc)
                     (ring/nmul nc denominator-ab))
          left-denominator (ring/nmul denominator-ab dc)
          right-numerator
          (ring/nadd (ring/nmul na denominator-bc)
                     (ring/nmul numerator-bc da))
          right-denominator (ring/nmul da denominator-bc)
          cross-left (ring/nmul left-numerator right-denominator)
          cross-right (ring/nmul right-numerator left-denominator)]
      (:proof (ring/prove-nat-eq cross-left cross-right))))})

;; a + (b + c) ~ b + (a + c).  This is deliberately derived from the general
;; laws rather than normalized again, exercising theorem reuse.
(def add-swap-right-spec
  {:name 'nnrat/add-swap-right
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (equivalent (add 'a (add 'b 'c))
                (add 'b (add 'a 'c))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (let [start (add 'a (add 'b 'c))
          grouped (add (add 'a 'b) 'c)
          swapped (add (add 'b 'a) 'c)
          finish (add 'b (add 'a 'c))
          unassociate
          (equivalent-symmetric
           grouped start
           (function/app (function/const* 'nnrat/add-associative [])
                         'a 'b 'c))
          commute-inside
          (add-respects
           (add 'a 'b) (add 'b 'a) 'c 'c
           (add-commutative 'a 'b)
           (equivalent-reflexive 'c))
          associate
          (function/app (function/const* 'nnrat/add-associative [])
                        'b 'a 'c)]
      (equivalent-transitive
       start grouped finish unassociate
       (equivalent-transitive grouped swapped finish
                              commute-inside associate))))})

;; (a+b)+(c+d) ~ (a+c)+(b+d), assembled exclusively from the installed
;; associativity/commutativity/congruence laws.
(def add-four-reorder-spec
  {:name 'nnrat/add-four-reorder
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (equivalent
     (add (add 'a 'b) (add 'c 'd))
     (add (add 'a 'c) (add 'b 'd))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (let [start (add (add 'a 'b) (add 'c 'd))
          first (add 'a (add 'b (add 'c 'd)))
          second (add 'a (add (add 'b 'c) 'd))
          third (add 'a (add (add 'c 'b) 'd))
          fourth (add 'a (add 'c (add 'b 'd)))
          finish (add (add 'a 'c) (add 'b 'd))
          step-one
          (function/app (function/const* 'nnrat/add-associative [])
                        'a 'b (add 'c 'd))
          step-two
          (add-respects
           'a 'a (add 'b (add 'c 'd)) (add (add 'b 'c) 'd)
           (equivalent-reflexive 'a)
           (equivalent-symmetric
            (add (add 'b 'c) 'd)
            (add 'b (add 'c 'd))
            (function/app (function/const* 'nnrat/add-associative [])
                          'b 'c 'd)))
          step-three
          (add-respects
           'a 'a (add (add 'b 'c) 'd) (add (add 'c 'b) 'd)
           (equivalent-reflexive 'a)
           (add-respects
            (add 'b 'c) (add 'c 'b) 'd 'd
            (add-commutative 'b 'c)
            (equivalent-reflexive 'd)))
          step-four
          (add-respects
           'a 'a (add (add 'c 'b) 'd) (add 'c (add 'b 'd))
           (equivalent-reflexive 'a)
           (function/app (function/const* 'nnrat/add-associative [])
                         'c 'b 'd))
          step-five
          (equivalent-symmetric
           finish fourth
           (function/app (function/const* 'nnrat/add-associative [])
                         'a 'c (add 'b 'd)))
          through-two
          (equivalent-transitive start first second step-one step-two)
          through-three
          (equivalent-transitive start second third through-two step-three)
          through-four
          (equivalent-transitive start third fourth through-three step-four)]
      (equivalent-transitive start fourth finish through-four step-five)))})

(def theorem-specs
  [add-associative-spec add-swap-right-spec add-four-reorder-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nnrat-additive-reassociation theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.additive-reassociation))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
