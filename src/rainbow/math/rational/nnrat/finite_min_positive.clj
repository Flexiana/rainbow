(ns rainbow.math.rational.nnrat.finite-min-positive
  "Positive lower bounds from finite exact-rational minima.

  The existing non-empty minimum fold takes an explicit initial value and a
  list of remaining values.  If every input is strictly positive, its result
  is strictly positive.  Combined with the fold's existing lower-bound law,
  this produces an exact positive value below every input—the quantitative
  finite-minimum ingredient for Markov minorization and mixing bounds.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]
            [rainbow.math.rational.nnrat.positive :as positive]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- app [f & xs] (apply function/app f xs))
(defn- nil-list []
  (app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-list [head tail]
  (app (function/const* 'data/cons [type-level]) nnrat head tail))
(defn- membership [items value]
  (app (function/const* 'list/membership [zero-level])
       nnrat items value))
(defn- positive-rational [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- minimum-fold [initial rest]
  (app (function/const* 'nnrat/min-ub []) initial rest))
(defn- lower-than-all [initial rest value]
  (app (function/const* 'nnrat/le-all []) initial rest value))
(defn- upper-rest [rest value]
  (app
   (function/const* 'data/List.rec [type-level type-level])
   nnrat
   (function/lam [['ignored list-nnrat]] 'Prop)
   (proposition/truth)
   (function/lam
    [['upper nnrat] ['tail list-nnrat] ['induction-hypothesis 'Prop]]
    (proposition/conjunction
     (at-most value 'upper) 'induction-hypothesis))
   rest))
(defn- eq-nnrat [left right]
  (function/equality type-level nnrat left right))
(defn- reflexive [value]
  (app (function/const* 'equality/reflexive [type-level])
       nnrat value))
(defn- left-disjunct [left right evidence]
  (app (function/const* 'proposition/left-disjunct [])
       left right evidence))
(defn- right-disjunct [left right evidence]
  (app (function/const* 'proposition/right-disjunct [])
       left right evidence))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- use-disjunction [left right result evidence on-left on-right]
  (app (function/const* 'proposition/use-disjunction [])
       left right result evidence on-left on-right))
(defn- explode [result contradiction]
  (app (function/const* 'proposition/explode []) result contradiction))
(defn- reverse-substitute [left right same predicate at-right]
  (app (function/const* 'equality/reverse-substitution [type-level])
       nnrat left right same predicate at-right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def min-ub-positive-spec
  (let [all-positive
        (fn [items]
          (function/forall
           [['value nnrat]
            ['member (membership items 'value)]]
           (positive-rational 'value)))
        motive
        (function/lam
         [['rest list-nnrat]]
         (function/forall
          [['initial nnrat]
           ['initial-positive (positive-rational 'initial)]
           ['rest-positive (all-positive 'rest)]]
          (positive-rational (minimum-fold 'initial 'rest))))]
    {:name 'nnrat/min-ub-positive
     :universes []
     :type
     (function/forall
      [['initial nnrat]
       ['rest list-nnrat]
       ['initial-positive (positive-rational 'initial)]
       ['rest-positive (all-positive 'rest)]]
      (positive-rational (minimum-fold 'initial 'rest)))
     :value
     (function/lam
      [['initial nnrat]
       ['rest list-nnrat]
       ['initial-positive (positive-rational 'initial)]
       ['rest-positive (all-positive 'rest)]]
      (app
       (app
        (function/const* 'data/List.rec [type-level zero-level])
        nnrat motive
        (function/lam
         [['first nnrat]
          ['first-positive (positive-rational 'first)]
          ['ignored-rest-positive (all-positive (nil-list))]]
         'first-positive)
        (function/lam
         [['head nnrat] ['tail list-nnrat]
          ['induction-hypothesis (app motive 'tail)]
          ['first nnrat]
          ['first-positive (positive-rational 'first)]
          ['all-positive-cons
           (all-positive (cons-list 'head 'tail))]]
         (let [head-same (eq-nnrat 'head 'head)
               head-member
               (left-disjunct
                head-same (membership 'tail 'head) (reflexive 'head))
               head-positive
               (app 'all-positive-cons 'head head-member)
               tail-positive
               (function/lam
                [['value nnrat]
                 ['member (membership 'tail 'value)]]
                (app
                 'all-positive-cons 'value
                 (right-disjunct
                  (eq-nnrat 'value 'head)
                  (membership 'tail 'value)
                  'member)))
               fold-positive
               (app 'induction-hypothesis
                    'first 'first-positive tail-positive)]
           (app
            (function/const* 'nnrat/min-positive [])
            'head (minimum-fold 'first 'tail)
            head-positive fold-positive)))
        'rest)
       'initial 'initial-positive 'rest-positive))}))

(def min-ub-positive-lower-bound-spec
  (let [all-positive
        (fn [items]
          (function/forall
           [['value nnrat]
            ['member (membership items 'value)]]
           (positive-rational 'value)))]
    {:name 'nnrat/min-ub-positive-lower-bound
     :universes []
     :type
     (function/forall
      [['initial nnrat]
       ['rest list-nnrat]
       ['initial-positive (positive-rational 'initial)]
       ['rest-positive (all-positive 'rest)]]
      (proposition/conjunction
       (positive-rational (minimum-fold 'initial 'rest))
       (lower-than-all
        'initial 'rest (minimum-fold 'initial 'rest))))
     :value
     (function/lam
      [['initial nnrat]
       ['rest list-nnrat]
       ['initial-positive (positive-rational 'initial)]
       ['rest-positive (all-positive 'rest)]]
      (conjoin
       (positive-rational (minimum-fold 'initial 'rest))
       (lower-than-all 'initial 'rest (minimum-fold 'initial 'rest))
       (app
        (function/const* 'nnrat/min-ub-positive [])
        'initial 'rest 'initial-positive 'rest-positive)
       (app
        (function/const* 'nnrat/min-ub-is-lower [])
        'initial 'rest)))}))

(def le-all-member-spec
  (let [motive
        (function/lam
         [['rest list-nnrat]]
         (function/forall
          [['initial nnrat] ['low nnrat]
           ['bounds (lower-than-all 'initial 'rest 'low)]
           ['value nnrat]
           ['member
            (membership (cons-list 'initial 'rest) 'value)]]
          (at-most 'low 'value)))]
    {:name 'nnrat/le-all-member
     :universes []
     :type
     (function/forall
      [['initial nnrat] ['rest list-nnrat] ['low nnrat]
       ['bounds (lower-than-all 'initial 'rest 'low)]
       ['value nnrat]
       ['member (membership (cons-list 'initial 'rest) 'value)]]
      (at-most 'low 'value))
     :value
     (function/lam
      [['initial nnrat] ['rest list-nnrat] ['low nnrat]
       ['bounds (lower-than-all 'initial 'rest 'low)]
       ['value nnrat]
       ['member (membership (cons-list 'initial 'rest) 'value)]]
      (app
       (app
        (function/const* 'data/List.rec [type-level zero-level])
        nnrat motive
        (function/lam
         [['first nnrat] ['lower nnrat]
          ['first-bounds
           (lower-than-all 'first (nil-list) 'lower)]
          ['candidate nnrat]
          ['candidate-member
           (membership (cons-list 'first (nil-list)) 'candidate)]]
         (use-disjunction
          (eq-nnrat 'candidate 'first)
          (membership (nil-list) 'candidate)
          (at-most 'lower 'candidate)
          'candidate-member
          (function/lam
           [['same (eq-nnrat 'candidate 'first)]]
           (reverse-substitute
            'candidate 'first 'same
            (function/lam
             [['other nnrat]] (at-most 'lower 'other))
            (left-conjunct
             (at-most 'lower 'first)
             (upper-rest (nil-list) 'lower)
             'first-bounds)))
          (function/lam
           [['impossible (membership (nil-list) 'candidate)]]
           (explode (at-most 'lower 'candidate) 'impossible))))
        (function/lam
         [['head nnrat] ['tail list-nnrat]
          ['induction-hypothesis (app motive 'tail)]
          ['first nnrat] ['lower nnrat]
          ['all-bounds
           (lower-than-all
            'first (cons-list 'head 'tail) 'lower)]
          ['candidate nnrat]
          ['candidate-member
           (membership
            (cons-list 'first (cons-list 'head 'tail))
            'candidate)]]
         (let [first-bound
               (left-conjunct
                (at-most 'lower 'first)
                (upper-rest (cons-list 'head 'tail) 'lower)
                'all-bounds)
               remaining-bounds
               (right-conjunct
                (at-most 'lower 'first)
                (upper-rest (cons-list 'head 'tail) 'lower)
                'all-bounds)]
           (use-disjunction
            (eq-nnrat 'candidate 'first)
            (membership (cons-list 'head 'tail) 'candidate)
            (at-most 'lower 'candidate)
            'candidate-member
            (function/lam
             [['same (eq-nnrat 'candidate 'first)]]
             (reverse-substitute
              'candidate 'first 'same
              (function/lam
               [['other nnrat]] (at-most 'lower 'other))
              first-bound))
            (function/lam
             [['remaining-member
               (membership
                (cons-list 'head 'tail) 'candidate)]]
             (app
              'induction-hypothesis
              'head 'lower remaining-bounds
              'candidate 'remaining-member)))))
        'rest)
       'initial 'low 'bounds 'value 'member))}))

(def min-ub-below-member-spec
  {:name 'nnrat/min-ub-below-member
   :universes []
   :type
   (function/forall
    [['initial nnrat] ['rest list-nnrat]
     ['value nnrat]
     ['member (membership (cons-list 'initial 'rest) 'value)]]
    (at-most (minimum-fold 'initial 'rest) 'value))
   :value
   (function/lam
    [['initial nnrat] ['rest list-nnrat]
     ['value nnrat]
     ['member (membership (cons-list 'initial 'rest) 'value)]]
    (app
     (function/const* 'nnrat/le-all-member [])
     'initial 'rest (minimum-fold 'initial 'rest)
     (app
      (function/const* 'nnrat/min-ub-is-lower [])
      'initial 'rest)
     'value 'member))})

(def definition-specs [])
(def theorem-specs
  [min-ub-positive-spec min-ub-positive-lower-bound-spec
   le-all-member-spec min-ub-below-member-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.nnrat.positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-finite-min-positive theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.finite-min-positive))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
