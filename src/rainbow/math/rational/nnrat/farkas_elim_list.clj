(ns rainbow.math.rational.nnrat.farkas-elim-list
  "List-sized one-variable Fourier--Motzkin elimination over nnrat bounds.

  Lower bounds are folded from zero with max, while the non-empty upper family
  is represented by a head and a list tail.  The reduced system says that the
  folded lower bound satisfies every upper bound.  Constructively, this is
  equivalent to existence of a value satisfying every lower and upper bound.
  All definitions and proofs are native proof data and axiom-free."
  (:refer-clojure :exclude [denominator numerator reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- base-at-most [left right]
  (function/app (function/const* 'nnrat/base-at-most []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- nat-add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- nat-multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- maximum [left right]
  (function/app (function/const* 'minmax/max []) left right))
(defn- minimum [left right]
  (function/app (function/const* 'minmax/min []) left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))

(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- min-ub [u0 urest]
  (function/app (function/const* 'nnrat/min-ub []) u0 urest))
(defn- reduced [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-reduced [])
                lowers u0 urest))
(defn- solvable [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-solvable [])
                lowers u0 urest))

(defn- upper-rest [urest value]
  (function/app
   (function/const* 'data/List.rec [type-level type-level])
   nnrat
   (function/lam [['ignored list-nnrat]] 'Prop)
   (proposition/truth)
   (function/lam
    [['upper nnrat] ['tail list-nnrat] ['ih 'Prop]]
    (proposition/conjunction (at-most value 'upper) 'ih))
   urest))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- at-most-reflexive [value]
  (function/app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))
(defn- max-upper-left [left right]
  (function/app (function/const* 'minmax/max-upper-left []) left right))
(defn- max-upper-right [left right]
  (function/app (function/const* 'minmax/max-upper-right []) left right))
(defn- at-most-max [left right high left-high right-high]
  (function/app (function/const* 'minmax/at-most-max [])
                left right high left-high right-high))
(defn- min-lower-left [left right]
  (function/app (function/const* 'minmax/min-lower-left []) left right))
(defn- min-lower-right [left right]
  (function/app (function/const* 'minmax/min-lower-right []) left right))
(defn- at-most-min [low left right low-left low-right]
  (function/app (function/const* 'minmax/at-most-min [])
                low left right low-left low-right))

;; Definitions -------------------------------------------------------------

(def ge-all-spec
  {:name 'nnrat/ge-all :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] 'Prop)
     (proposition/truth)
     (function/lam
      [['lower nnrat] ['tail list-nnrat] ['ih 'Prop]]
      (proposition/conjunction (at-most 'lower 'value) 'ih))
     'lowers))})

(def le-all-spec
  {:name 'nnrat/le-all :kind :definition :universes []
   :type (function/arrow nnrat list-nnrat nnrat 'Prop)
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['value nnrat]]
    (proposition/conjunction
     (at-most 'value 'u0)
     (upper-rest 'urest 'value)))})

(def max-lb-spec
  {:name 'nnrat/max-lb :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value
   (function/lam
    [['lowers list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nnrat)
     nnrat-zero
     (function/lam
      [['lower nnrat] ['tail list-nnrat] ['ih nnrat]]
      (maximum 'lower 'ih))
     'lowers))})

(def min-ub-spec
  {:name 'nnrat/min-ub :kind :definition :universes []
   :type (function/arrow nnrat list-nnrat nnrat)
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nnrat)
     'u0
     (function/lam
      [['upper nnrat] ['tail list-nnrat] ['ih nnrat]]
      (minimum 'upper 'ih))
     'urest))})

(def reduced-spec
  {:name 'nnrat/farkas-elim-list-reduced :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (le-all 'u0 'urest (max-lb 'lowers)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-list-solvable :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (proposition/conjunction
       (ge-all 'lowers 'value)
       (le-all 'u0 'urest 'value)))))})

(def definition-specs
  [ge-all-spec le-all-spec max-lb-spec min-ub-spec reduced-spec solvable-spec])

;; A native zero lower bound.  There is no exported nnrat version in the D63
;; environment, so build the cross-product Nat witness explicitly.
(def zero-at-most-spec
  {:name 'nnrat/zero-at-most :universes []
   :type (function/forall [['value nnrat]] (at-most nnrat-zero 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [right-cross
          (nat-multiply (numerator 'value) (denominator nnrat-zero))
          cross-proof
          (function/app
           (function/const* 'proposition/witness [type-level])
           nat
           (function/lam
            [['extra nat]]
            (nat-equality (nat-add (function/const* 'data/zero []) 'extra)
                          right-cross))
           right-cross
           (function/app (function/const* 'equality/reflexive [type-level])
                         nat right-cross))]
      (function/app (function/const* 'nnrat/at-most-from-cross [])
                    nnrat-zero 'value cross-proof)))})

;; Every element is below the max fold.  The strengthened motive says that any
;; high bound above the fold also bounds the whole list.
(def max-lb-is-upper-spec
  (let [motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['high nnrat]
           ['fold-at-most-high (at-most (max-lb 'ys) 'high)]]
          (ge-all 'ys 'high)))]
    {:name 'nnrat/max-lb-is-upper :universes []
     :type (function/forall [['lowers list-nnrat]]
                            (ge-all 'lowers (max-lb 'lowers)))
     :value
     (function/lam
      [['lowers list-nnrat]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nnrat motive
       (function/lam
        [['high nnrat] ['ignored (at-most nnrat-zero 'high)]]
        (function/const* 'proposition/trivial []))
       (function/lam
        [['lower nnrat] ['tail list-nnrat]
         ['ih (function/app motive 'tail)]
         ['high nnrat]
         ['fold-at-most-high
          (at-most (maximum 'lower (max-lb 'tail)) 'high)]]
        (let [folded (maximum 'lower (max-lb 'tail))
              lower-high
              (at-most-transitive
               'lower folded 'high
               (max-upper-left 'lower (max-lb 'tail))
               'fold-at-most-high)
              tail-fold-high
              (at-most-transitive
               (max-lb 'tail) folded 'high
               (max-upper-right 'lower (max-lb 'tail))
               'fold-at-most-high)
              tail-high (function/app 'ih 'high tail-fold-high)]
          (conjoin (at-most 'lower 'high) (ge-all 'tail 'high)
                   lower-high tail-high)))
       'lowers
       (max-lb 'lowers)
       (at-most-reflexive (max-lb 'lowers))))}))

;; If v bounds every list element, it bounds their max fold.
(def max-lb-least-spec
  (let [motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['value nnrat] ['all (ge-all 'ys 'value)]]
          (at-most (max-lb 'ys) 'value)))]
    {:name 'nnrat/max-lb-least :universes []
     :type
     (function/forall
      [['lowers list-nnrat] ['value nnrat]
       ['all (ge-all 'lowers 'value)]]
      (at-most (max-lb 'lowers) 'value))
     :value
     (function/lam
      [['lowers list-nnrat] ['value nnrat]
       ['all (ge-all 'lowers 'value)]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nnrat motive
       (function/lam
        [['candidate nnrat] ['ignored (ge-all
                                      (function/app
                                       (function/const* 'data/nil [type-level])
                                       nnrat)
                                      'candidate)]]
        (function/app (function/const* 'nnrat/zero-at-most []) 'candidate))
       (function/lam
        [['lower nnrat] ['tail list-nnrat]
         ['ih (function/app motive 'tail)]
         ['candidate nnrat]
         ['bounds (ge-all (cons-nnrat 'lower 'tail) 'candidate)]]
        (let [head-bound
              (left-conjunct (at-most 'lower 'candidate)
                             (ge-all 'tail 'candidate) 'bounds)
              tail-bounds
              (right-conjunct (at-most 'lower 'candidate)
                              (ge-all 'tail 'candidate) 'bounds)
              tail-fold-bound (function/app 'ih 'candidate tail-bounds)]
          (at-most-max 'lower (max-lb 'tail) 'candidate
                       head-bound tail-fold-bound)))
       'lowers 'value 'all))}))

;; Moving the candidate down preserves all upper-bound constraints.
(def le-all-antitone-spec
  (let [rest-motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['a nnrat] ['b nnrat] ['a-b (at-most 'a 'b)]
           ['all-b (upper-rest 'ys 'b)]]
          (upper-rest 'ys 'a)))]
    {:name 'nnrat/le-all-antitone :universes []
     :type
     (function/forall
      [['u0 nnrat] ['urest list-nnrat] ['a nnrat] ['b nnrat]
       ['a-b (at-most 'a 'b)] ['all-b (le-all 'u0 'urest 'b)]]
      (le-all 'u0 'urest 'a))
     :value
     (function/lam
      [['u0 nnrat] ['urest list-nnrat] ['a nnrat] ['b nnrat]
       ['a-b (at-most 'a 'b)] ['all-b (le-all 'u0 'urest 'b)]]
      (let [b-u0
            (left-conjunct (at-most 'b 'u0) (upper-rest 'urest 'b) 'all-b)
            rest-b
            (right-conjunct (at-most 'b 'u0) (upper-rest 'urest 'b) 'all-b)
            rest-a
            (function/app
             (function/const* 'data/List.rec [type-level zero-level])
             nnrat rest-motive
             (function/lam
              [['low nnrat] ['high nnrat] ['ordered (at-most 'low 'high)]
               ['ignored (upper-rest
                          (function/app
                           (function/const* 'data/nil [type-level]) nnrat)
                          'high)]]
              (function/const* 'proposition/trivial []))
             (function/lam
              [['upper nnrat] ['tail list-nnrat]
               ['ih (function/app rest-motive 'tail)]
               ['low nnrat] ['high nnrat] ['ordered (at-most 'low 'high)]
               ['bounds (upper-rest (cons-nnrat 'upper 'tail) 'high)]]
              (let [high-upper
                    (left-conjunct (at-most 'high 'upper)
                                   (upper-rest 'tail 'high) 'bounds)
                    tail-bounds
                    (right-conjunct (at-most 'high 'upper)
                                    (upper-rest 'tail 'high) 'bounds)]
                (conjoin
                 (at-most 'low 'upper) (upper-rest 'tail 'low)
                 (at-most-transitive 'low 'high 'upper
                                     'ordered high-upper)
                 (function/app 'ih 'low 'high 'ordered tail-bounds))))
             'urest 'a 'b 'a-b rest-b)]
        (conjoin
         (at-most 'a 'u0) (upper-rest 'urest 'a)
         (at-most-transitive 'a 'b 'u0 'a-b b-u0)
         rest-a)))}))

;; The min fold is below its head and every tail upper.
(def min-ub-is-lower-spec
  (let [motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['first nnrat] ['low nnrat]
           ['low-fold (at-most 'low (min-ub 'first 'ys))]]
          (le-all 'first 'ys 'low)))]
    {:name 'nnrat/min-ub-is-lower :universes []
     :type
     (function/forall
      [['u0 nnrat] ['urest list-nnrat]]
      (le-all 'u0 'urest (min-ub 'u0 'urest)))
     :value
     (function/lam
      [['u0 nnrat] ['urest list-nnrat]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nnrat motive
       (function/lam
        [['first nnrat] ['low nnrat] ['low-first (at-most 'low 'first)]]
        (conjoin (at-most 'low 'first)
                 (upper-rest
                  (function/app (function/const* 'data/nil [type-level]) nnrat)
                  'low)
                 'low-first (function/const* 'proposition/trivial [])))
       (function/lam
        [['upper nnrat] ['tail list-nnrat]
         ['ih (function/app motive 'tail)]
         ['first nnrat] ['low nnrat]
         ['low-fold
          (at-most 'low (minimum 'upper (min-ub 'first 'tail)))]]
        (let [low-upper
              (at-most-transitive
               'low (minimum 'upper (min-ub 'first 'tail)) 'upper
               'low-fold (min-lower-left 'upper (min-ub 'first 'tail)))
              low-tail-fold
              (at-most-transitive
               'low (minimum 'upper (min-ub 'first 'tail))
               (min-ub 'first 'tail)
               'low-fold (min-lower-right 'upper (min-ub 'first 'tail)))
              tail-result (function/app 'ih 'first 'low low-tail-fold)
              low-first
              (left-conjunct (at-most 'low 'first)
                             (upper-rest 'tail 'low) tail-result)
              low-tail
              (right-conjunct (at-most 'low 'first)
                              (upper-rest 'tail 'low) tail-result)]
          (conjoin
           (at-most 'low 'first)
           (upper-rest (cons-nnrat 'upper 'tail) 'low)
           low-first
           (conjoin (at-most 'low 'upper) (upper-rest 'tail 'low)
                    low-upper low-tail))))
       'urest 'u0 (min-ub 'u0 'urest)
       (at-most-reflexive (min-ub 'u0 'urest))))}))

;; Any value below all uppers is below their min fold.
(def min-ub-greatest-spec
  (let [motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['first nnrat] ['value nnrat]
           ['all (le-all 'first 'ys 'value)]]
          (at-most 'value (min-ub 'first 'ys))))]
    {:name 'nnrat/min-ub-greatest :universes []
     :type
     (function/forall
      [['u0 nnrat] ['urest list-nnrat] ['value nnrat]
       ['all (le-all 'u0 'urest 'value)]]
      (at-most 'value (min-ub 'u0 'urest)))
     :value
     (function/lam
      [['u0 nnrat] ['urest list-nnrat] ['value nnrat]
       ['all (le-all 'u0 'urest 'value)]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nnrat motive
       (function/lam
        [['first nnrat] ['candidate nnrat]
         ['bounds (le-all
                   'first
                   (function/app (function/const* 'data/nil [type-level]) nnrat)
                   'candidate)]]
        (left-conjunct (at-most 'candidate 'first)
                       (upper-rest
                        (function/app (function/const* 'data/nil [type-level]) nnrat)
                        'candidate)
                       'bounds))
       (function/lam
        [['upper nnrat] ['tail list-nnrat]
         ['ih (function/app motive 'tail)]
         ['first nnrat] ['candidate nnrat]
         ['bounds (le-all 'first (cons-nnrat 'upper 'tail) 'candidate)]]
        (let [candidate-first
              (left-conjunct
               (at-most 'candidate 'first)
               (upper-rest (cons-nnrat 'upper 'tail) 'candidate) 'bounds)
              rest-bounds
              (right-conjunct
               (at-most 'candidate 'first)
               (upper-rest (cons-nnrat 'upper 'tail) 'candidate) 'bounds)
              candidate-upper
              (left-conjunct (at-most 'candidate 'upper)
                             (upper-rest 'tail 'candidate) rest-bounds)
              candidate-tail
              (right-conjunct (at-most 'candidate 'upper)
                              (upper-rest 'tail 'candidate) rest-bounds)
              tail-all
              (conjoin (at-most 'candidate 'first)
                       (upper-rest 'tail 'candidate)
                       candidate-first candidate-tail)
              candidate-tail-min (function/app 'ih 'first 'candidate tail-all)]
          (at-most-min 'candidate 'upper (min-ub 'first 'tail)
                       candidate-upper candidate-tail-min)))
       'urest 'u0 'value 'all))}))

(def extends-spec
  {:name 'nnrat/farkas-elim-list-extends :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest)]]
    (solvable 'lowers 'u0 'urest))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest)]]
    (let [value (max-lb 'lowers)
          predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (ge-all 'lowers 'candidate)
            (le-all 'u0 'urest 'candidate)))
          satisfies
          (conjoin (ge-all 'lowers value) (le-all 'u0 'urest value)
                   (function/app (function/const* 'nnrat/max-lb-is-upper [])
                                 'lowers)
                   'reduced-feasible)]
      (function/app (function/const* 'proposition/witness [type-level])
                    nnrat predicate value satisfies)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-list-projects :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['solution (solvable 'lowers 'u0 'urest)]]
    (reduced 'lowers 'u0 'urest))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['solution (solvable 'lowers 'u0 'urest)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (ge-all 'lowers 'candidate)
            (le-all 'u0 'urest 'candidate)))]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nnrat predicate (reduced 'lowers 'u0 'urest) 'solution
       (function/lam
        [['value nnrat]
         ['satisfies
          (proposition/conjunction
           (ge-all 'lowers 'value) (le-all 'u0 'urest 'value))]]
        (let [lower-bounds
              (left-conjunct (ge-all 'lowers 'value)
                             (le-all 'u0 'urest 'value) 'satisfies)
              upper-bounds
              (right-conjunct (ge-all 'lowers 'value)
                              (le-all 'u0 'urest 'value) 'satisfies)
              folded-lower-at-most-value
              (function/app (function/const* 'nnrat/max-lb-least [])
                            'lowers 'value lower-bounds)]
          (function/app (function/const* 'nnrat/le-all-antitone [])
                        'u0 'urest (max-lb 'lowers) 'value
                        folded-lower-at-most-value upper-bounds))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-list-solvable-iff :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (proposition/equivalence
     (reduced 'lowers 'u0 'urest)
     (solvable 'lowers 'u0 'urest)))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (let [reduced-prop (reduced 'lowers 'u0 'urest)
          solvable-prop (solvable 'lowers 'u0 'urest)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app (function/const* 'nnrat/farkas-elim-list-extends [])
                      'lowers 'u0 'urest 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app (function/const* 'nnrat/farkas-elim-list-projects [])
                      'lowers 'u0 'urest 'solution)))))})

(def theorem-specs
  [zero-at-most-spec
   max-lb-is-upper-spec max-lb-least-spec le-all-antitone-spec
   min-ub-is-lower-spec min-ub-greatest-spec
   extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-list (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-list))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
