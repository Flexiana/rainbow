(ns rainbow.math.rational.nnrat.lp-multi-constraint-duality
  "Finite positive-constraint, one-variable LP duality over nnrat.

  A constraint is stored as ((ap,adp),(bp,bdp)) and denotes

      make(succ ap,adp) * x <= make(succ bp,bdp).

  Thus positivity of both coefficients is structural.  A non-empty family is
  represented by one constraint's four parameters and a list of remaining
  constraints.  Its canonical primal point is the `min-ub` fold of all b/a
  ratios.  We prove that point feasible, largest among feasible points, and
  objective-optimal for every nonnegative objective coefficient.

  The final theorem additionally accepts evidence that the head constraint is
  binding.  It constructs the concentrated dual weight c/a at that constraint,
  proves dual feasibility and zero gap, and packages primal strong duality.
  This is the explicit-binding-index form of finite multi-constraint strong
  duality; extracting such an index from the fold is deliberately separate.

  Every declaration is native proof data and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.lp-strong-duality-general :as single]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))
(def nat-pair
  (function/app (function/const* 'data/Product [type-level type-level])
                nat nat))
(def positive-constraint
  (function/app (function/const* 'data/Product [type-level type-level])
                nat-pair nat-pair))
(def list-positive-constraint
  (function/app (function/const* 'data/List [type-level]) positive-constraint))

(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- constraint-a-pair [constraint]
  (first-of nat-pair nat-pair constraint))
(defn- constraint-b-pair [constraint]
  (second-of nat-pair nat-pair constraint))
(defn- constraint-ap [constraint]
  (first-of nat nat (constraint-a-pair constraint)))
(defn- constraint-adp [constraint]
  (second-of nat nat (constraint-a-pair constraint)))
(defn- constraint-bp [constraint]
  (first-of nat nat (constraint-b-pair constraint)))
(defn- constraint-bdp [constraint]
  (second-of nat nat (constraint-b-pair constraint)))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- positive [numerator-predecessor denominator-predecessor]
  (make (succ numerator-predecessor) denominator-predecessor))
(defn- constraint-a [constraint]
  (positive (constraint-ap constraint) (constraint-adp constraint)))
(defn- constraint-b [constraint]
  (positive (constraint-bp constraint) (constraint-bdp constraint)))
(defn- constraint-ratio [constraint]
  (function/app (function/const* 'nnrat/divide [])
                (constraint-b constraint) (constraint-a constraint)))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- nil-nnrat []
  (function/app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(defn- constraint-ratios [constraints]
  (function/app (function/const* 'nnrat/lp-positive-constraint-ratios [])
                constraints))
(defn- constraints-feasible [constraints value]
  (function/app (function/const* 'nnrat/lp-positive-constraints-feasible [])
                constraints value))
(defn- min-ub [u0 urest]
  (function/app (function/const* 'nnrat/min-ub []) u0 urest))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))

;; This is definitionally the tail of `le-all`; naming it locally keeps the
;; normalization induction small without adding a redundant public constant.
(defn- upper-rest [ratios value]
  (function/app
   (function/const* 'data/List.rec [type-level type-level])
   nnrat
   (function/lam [['ignored list-nnrat]] 'Prop)
   (proposition/truth)
   (function/lam
    [['upper nnrat] ['ratio-tail list-nnrat] ['ih 'Prop]]
    (proposition/conjunction (at-most value 'upper) 'ih))
   ratios))

(defn- head-ratio [ap adp bp bdp]
  (divide (positive bp bdp) (positive ap adp)))
(defn- primal-solution [ap adp bp bdp tail]
  (min-ub (head-ratio ap adp bp bdp) (constraint-ratios tail)))
(defn- head-feasible [ap adp bp bdp value]
  (at-most (multiply (positive ap adp) value) (positive bp bdp)))
(defn- family-feasible [ap adp bp bdp tail value]
  (proposition/conjunction
   (head-feasible ap adp bp bdp value)
   (constraints-feasible tail value)))
(defn- primal-optimal [ap adp bp bdp tail c value]
  (function/forall
   [['alternative nnrat]
    ['alternative-feasible
     (family-feasible ap adp bp bdp tail 'alternative)]]
   (at-most (multiply c 'alternative) (multiply c value))))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- equivalence-intro [left right forward backward]
  (function/app (function/const* 'proposition/equivalence-intro [])
                left right forward backward))
(defn- equivalence-forward [left right iff evidence]
  (function/app (function/const* 'proposition/equivalence-forward [])
                left right iff evidence))
(defn- equivalence-backward [left right iff evidence]
  (function/app (function/const* 'proposition/equivalence-backward [])
                left right iff evidence))
(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))
(defn- equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- multiply-respects [left equivalent-left right equivalent-right
                           same-left same-right]
  (function/app
   (function/const* 'nnrat/multiply-respects-equivalence [])
   left equivalent-left right equivalent-right same-left same-right))
(defn- at-most-respects [left equivalent-left right equivalent-right
                          same-left same-right ordered]
  (function/app
   (function/const* 'nnrat/at-most-respects-equivalence [])
   left equivalent-left right equivalent-right
   same-left same-right ordered))
(defn- multiply-monotone [factor left right ordered]
  (function/app (function/const* 'nnrat/multiply-monotone [])
                factor left right ordered))
(defn- normalize-upper [ap adp value bound]
  (function/app
   (function/const* 'nnrat/at-most-multiply-left-normalize-upper [])
   ap adp value bound))
(defn- multiply-divide-cancel [np dp value]
  (function/app (function/const* 'nnrat/multiply-divide-cancel [])
                np dp value))
(defn- multiply-swap-right [a b c]
  (function/app (function/const* 'nnrat/multiply-swap-right []) a b c))

;; Definitions -------------------------------------------------------------

(def constraint-ratios-spec
  {:name 'nnrat/lp-positive-constraint-ratios
   :kind :definition :universes []
   :type (function/arrow list-positive-constraint list-nnrat)
   :value
   (function/lam
    [['constraints list-positive-constraint]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     positive-constraint
     (function/lam [['ignored list-positive-constraint]] list-nnrat)
     (nil-nnrat)
     (function/lam
      [['constraint positive-constraint]
       ['tail list-positive-constraint]
       ['ih list-nnrat]]
      (cons-nnrat (constraint-ratio 'constraint) 'ih))
     'constraints))})

(def constraints-feasible-spec
  {:name 'nnrat/lp-positive-constraints-feasible
   :kind :definition :universes []
   :type (function/arrow list-positive-constraint nnrat 'Prop)
   :value
   (function/lam
    [['constraints list-positive-constraint] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     positive-constraint
     (function/lam [['ignored list-positive-constraint]] 'Prop)
     (proposition/truth)
     (function/lam
      [['constraint positive-constraint]
       ['tail list-positive-constraint]
       ['ih 'Prop]]
      (proposition/conjunction
       (at-most (multiply (constraint-a 'constraint) 'value)
                (constraint-b 'constraint))
       'ih))
     'constraints))})

(def definition-specs [constraint-ratios-spec constraints-feasible-spec])

;; Positive coefficient normalization commutes with the whole list.  This is
;; the bridge from actual a*x<=b constraints to the `min-ub` LIST machinery.
(def constraints-normalize-upper-spec
  (let [motive
        (function/lam
         [['ys list-positive-constraint]]
         (function/forall
          [['value nnrat]]
          (proposition/equivalence
           (constraints-feasible 'ys 'value)
           (upper-rest (constraint-ratios 'ys) 'value))))]
    {:name 'nnrat/lp-positive-constraints-normalize-upper
     :universes []
     :type
     (function/forall
      [['constraints list-positive-constraint] ['value nnrat]]
      (proposition/equivalence
       (constraints-feasible 'constraints 'value)
       (upper-rest (constraint-ratios 'constraints) 'value)))
     :value
     (function/lam
      [['constraints list-positive-constraint] ['value nnrat]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       positive-constraint motive
       (function/lam
        [['candidate nnrat]]
        (equivalence-intro
         (proposition/truth) (proposition/truth)
         (function/lam [['ignored (proposition/truth)]]
                       (function/const* 'proposition/trivial []))
         (function/lam [['ignored (proposition/truth)]]
                       (function/const* 'proposition/trivial []))))
       (function/lam
        [['constraint positive-constraint]
         ['tail list-positive-constraint]
         ['ih (function/app motive 'tail)]
         ['candidate nnrat]]
        (let [ap (constraint-ap 'constraint)
              adp (constraint-adp 'constraint)
              b (constraint-b 'constraint)
              original
              (proposition/conjunction
               (at-most (multiply (constraint-a 'constraint) 'candidate) b)
               (constraints-feasible 'tail 'candidate))
              normalized
              (proposition/conjunction
               (at-most 'candidate (constraint-ratio 'constraint))
               (upper-rest (constraint-ratios 'tail) 'candidate))
              head-original
              (at-most (multiply (constraint-a 'constraint) 'candidate) b)
              head-normalized
              (at-most 'candidate (constraint-ratio 'constraint))
              tail-original (constraints-feasible 'tail 'candidate)
              tail-normalized
              (upper-rest (constraint-ratios 'tail) 'candidate)
              head-iff (normalize-upper ap adp 'candidate b)
              tail-iff (function/app 'ih 'candidate)]
          (equivalence-intro
           original normalized
           (function/lam
            [['evidence original]]
            (conjoin
             head-normalized tail-normalized
             (equivalence-forward
              head-original head-normalized head-iff
              (left-conjunct head-original tail-original 'evidence))
             (equivalence-forward
              tail-original tail-normalized tail-iff
              (right-conjunct head-original tail-original 'evidence))))
           (function/lam
            [['evidence normalized]]
            (conjoin
             head-original tail-original
             (equivalence-backward
              head-original head-normalized head-iff
              (left-conjunct head-normalized tail-normalized 'evidence))
             (equivalence-backward
              tail-original tail-normalized tail-iff
              (right-conjunct head-normalized tail-normalized 'evidence)))))))
       'constraints 'value))}))

(def primal-feasible-spec
  {:name 'nnrat/lp-positive-multi-primal-feasible
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint]]
    (family-feasible
     'ap 'adp 'bp 'bdp 'tail
     (primal-solution 'ap 'adp 'bp 'bdp 'tail)))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint]]
    (let [u0 (head-ratio 'ap 'adp 'bp 'bdp)
          ratios (constraint-ratios 'tail)
          x (min-ub u0 ratios)
          head-prop (head-feasible 'ap 'adp 'bp 'bdp x)
          tail-prop (constraints-feasible 'tail x)
          all-lower
          (function/app (function/const* 'nnrat/min-ub-is-lower [])
                        u0 ratios)
          head-order
          (left-conjunct (at-most x u0) (upper-rest ratios x) all-lower)
          tail-orders
          (right-conjunct (at-most x u0) (upper-rest ratios x) all-lower)
          head-proof
          (equivalence-backward
           head-prop (at-most x u0)
           (normalize-upper 'ap 'adp x (positive 'bp 'bdp))
           head-order)
          tail-proof
          (equivalence-backward
           tail-prop (upper-rest ratios x)
           (function/app
            (function/const* 'nnrat/lp-positive-constraints-normalize-upper [])
            'tail x)
           tail-orders)]
      (conjoin head-prop tail-prop head-proof tail-proof)))})

(def primal-largest-spec
  {:name 'nnrat/lp-positive-multi-primal-largest
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['value nnrat]
     ['feasible (family-feasible
                 'ap 'adp 'bp 'bdp 'tail 'value)]]
    (at-most 'value (primal-solution 'ap 'adp 'bp 'bdp 'tail)))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['value nnrat]
     ['feasible (family-feasible
                 'ap 'adp 'bp 'bdp 'tail 'value)]]
    (let [u0 (head-ratio 'ap 'adp 'bp 'bdp)
          ratios (constraint-ratios 'tail)
          head-prop (head-feasible 'ap 'adp 'bp 'bdp 'value)
          tail-prop (constraints-feasible 'tail 'value)
          head-proof (left-conjunct head-prop tail-prop 'feasible)
          tail-proof (right-conjunct head-prop tail-prop 'feasible)
          head-order
          (equivalence-forward
           head-prop (at-most 'value u0)
           (normalize-upper 'ap 'adp 'value (positive 'bp 'bdp))
           head-proof)
          tail-orders
          (equivalence-forward
           tail-prop (upper-rest ratios 'value)
           (function/app
            (function/const* 'nnrat/lp-positive-constraints-normalize-upper [])
            'tail 'value)
           tail-proof)
          all-orders
          (conjoin (at-most 'value u0) (upper-rest ratios 'value)
                   head-order tail-orders)]
      (function/app (function/const* 'nnrat/min-ub-greatest [])
                    u0 ratios 'value all-orders)))})

(def primal-optimal-spec
  {:name 'nnrat/lp-positive-multi-primal-optimal
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['c nnrat]]
    (primal-optimal
     'ap 'adp 'bp 'bdp 'tail 'c
     (primal-solution 'ap 'adp 'bp 'bdp 'tail)))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['c nnrat]
     ['alternative nnrat]
     ['alternative-feasible
      (family-feasible
       'ap 'adp 'bp 'bdp 'tail 'alternative)]]
    (let [x (primal-solution 'ap 'adp 'bp 'bdp 'tail)
          variable-order
          (function/app
           (function/const* 'nnrat/lp-positive-multi-primal-largest [])
           'ap 'adp 'bp 'bdp 'tail 'alternative 'alternative-feasible)]
      (multiply-monotone 'c 'alternative x variable-order)))})

;; Explicit binding-index strong duality.  The binding constraint is placed at
;; the head; `binding` is the propositional transport showing that its b/a is
;; the list minimum.  The dual vector is concentrated there, so its feasibility
;; and objective reduce definitionally to a*(c/a)>=c and b*(c/a).
(def head-binding-strong-duality-spec
  {:name 'nnrat/lp-positive-multi-head-binding-strong-duality
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['c nnrat]
     ['binding
      (equivalent
       (head-ratio 'ap 'adp 'bp 'bdp)
       (primal-solution 'ap 'adp 'bp 'bdp 'tail))]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          x (primal-solution 'ap 'adp 'bp 'bdp 'tail)
          y (divide 'c a)]
      (proposition/conjunction
       (family-feasible 'ap 'adp 'bp 'bdp 'tail x)
       (proposition/conjunction
        (at-most 'c (multiply a y))
        (proposition/conjunction
         (equivalent (multiply 'c x) (multiply b y))
         (primal-optimal 'ap 'adp 'bp 'bdp 'tail 'c x))))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['tail list-positive-constraint] ['c nnrat]
     ['binding
      (equivalent
       (head-ratio 'ap 'adp 'bp 'bdp)
       (primal-solution 'ap 'adp 'bp 'bdp 'tail))]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          ratio (head-ratio 'ap 'adp 'bp 'bdp)
          x (primal-solution 'ap 'adp 'bp 'bdp 'tail)
          y (divide 'c a)
          ay (multiply a y)
          aratio (multiply a ratio)
          cancel-a-c (multiply-divide-cancel 'ap 'adp 'c)
          cancel-a-b (multiply-divide-cancel 'ap 'adp b)
          hd
          (at-most-respects
           'c 'c ay 'c
           (equivalent-reflexive 'c) cancel-a-c
           (function/app (function/const* 'nnrat/at-most-reflexive []) 'c))
          c-to-ay (equivalent-symmetric ay 'c cancel-a-c)
          first
          (multiply-respects
           'c ay ratio ratio c-to-ay (equivalent-reflexive ratio))
          swapped (multiply-swap-right a y ratio)
          replace-aratio
          (multiply-respects
           aratio b y y cancel-a-b (equivalent-reflexive y))
          through-swap
          (equivalent-transitive
           (multiply 'c ratio) (multiply ay ratio) (multiply aratio y)
           first swapped)
          scalar-gap
          (equivalent-transitive
           (multiply 'c ratio) (multiply aratio y) (multiply b y)
           through-swap replace-aratio)
          c-binding
          (multiply-respects 'c 'c ratio x
                             (equivalent-reflexive 'c) 'binding)
          gap
          (equivalent-transitive
           (multiply 'c x) (multiply 'c ratio) (multiply b y)
           (equivalent-symmetric
            (multiply 'c ratio) (multiply 'c x) c-binding)
           scalar-gap)
          hp
          (function/app
           (function/const* 'nnrat/lp-positive-multi-primal-feasible [])
           'ap 'adp 'bp 'bdp 'tail)
          optimal
          (function/app
           (function/const* 'nnrat/lp-positive-multi-primal-optimal [])
           'ap 'adp 'bp 'bdp 'tail 'c)]
      (conjoin
       (family-feasible 'ap 'adp 'bp 'bdp 'tail x)
       (proposition/conjunction
        (at-most 'c (multiply a y))
        (proposition/conjunction
         (equivalent (multiply 'c x) (multiply b y))
         (primal-optimal 'ap 'adp 'bp 'bdp 'tail 'c x)))
       hp
       (conjoin
        (at-most 'c (multiply a y))
        (proposition/conjunction
         (equivalent (multiply 'c x) (multiply b y))
         (primal-optimal 'ap 'adp 'bp 'bdp 'tail 'c x))
        hd
        (conjoin
         (equivalent (multiply 'c x) (multiply b y))
         (primal-optimal 'ap 'adp 'bp 'bdp 'tail 'c x)
         gap optimal)))))})

(def theorem-specs
  [constraints-normalize-upper-spec
   primal-feasible-spec
   primal-largest-spec
   primal-optimal-spec
   head-binding-strong-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.lp-strong-duality-general])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-lp-multi-constraint-duality (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.lp-multi-constraint-duality))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
