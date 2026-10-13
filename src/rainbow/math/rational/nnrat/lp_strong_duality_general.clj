(ns rainbow.math.rational.nnrat.lp-strong-duality-general
  "Constructive strong duality for a parametric scalar LP.

  For positive rationals a and b and an arbitrary nonnegative rational c,

      maximize c*x subject to a*x <= b
      minimize b*y subject to c <= a*y,

  the matching-dual system for a primal-feasible x normalizes to the finite
  Farkas chain interval

      c/a <= y <= (c*x)/b.

  The encoding is exact: a feasible zero-gap dual gives a chain witness, while
  a chain witness proves that the canonical y=(c*x)/b is dual feasible and has
  zero gap.  The constructive chain alternative therefore gives either a
  zero-gap dual (and primal optimality) or both a refutation of every matching
  dual and the reduced-system Farkas infeasibility certificate.

  At x=b/a and y=c/a the interval is inhabited, yielding strong duality and
  primal/dual optimality for the whole positive-coefficient scalar family.
  All declarations are native proof data and axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-alternative :as alternative]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as right-monotone]
            [rainbow.math.rational.nnrat.order-scale :as scale]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

;; Public chain data representation: (lowers, (upper-head, upper-tail)).
(def upper-family
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat list-nnrat))
(def layer
  (function/app (function/const* 'data/Product [type-level type-level])
                list-nnrat upper-family))
(def list-layer
  (function/app (function/const* 'data/List [type-level]) layer))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
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
(defn- nil-nnrat [] (nil-of nnrat))
(defn- nil-layer [] (nil-of layer))
(defn- cons-nnrat [head tail] (cons-of nnrat head tail))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- chain-open-solvable [layers survivor]
  (function/app
   (function/const* 'nnrat/farkas-elim-chain-open-solvable [])
   layers survivor))
(defn- chain-solvable [layers terminal-lowers terminal-u0 terminal-urest]
  (function/app (function/const* 'nnrat/farkas-elim-chain-solvable [])
                layers terminal-lowers terminal-u0 terminal-urest))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- left-disjunct [left right evidence]
  (function/app (function/const* 'proposition/left-disjunct [])
                left right evidence))
(defn- right-disjunct [left right evidence]
  (function/app (function/const* 'proposition/right-disjunct [])
                left right evidence))
(defn- use-disjunction [left right result evidence on-left on-right]
  (function/app (function/const* 'proposition/use-disjunction [])
                left right result evidence on-left on-right))
(defn- witness [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat predicate value evidence))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nnrat predicate result evidence continue))
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
(defn- at-most-reflexive [value]
  (function/app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))
(defn- multiply-monotone [factor left right ordered]
  (function/app (function/const* 'nnrat/multiply-monotone [])
                factor left right ordered))
(defn- multiply-right-monotone [left right factor ordered]
  (function/app (function/const* 'nnrat/multiply-right-monotone [])
                left right factor ordered))
(defn- multiply-swap-right [a b c]
  (function/app (function/const* 'nnrat/multiply-swap-right []) a b c))
(defn- multiply-divide-cancel [np dp value]
  (function/app (function/const* 'nnrat/multiply-divide-cancel [])
                np dp value))
(defn- normalize-upper [np dp value bound]
  (function/app
   (function/const* 'nnrat/at-most-multiply-left-normalize-upper [])
   np dp value bound))
(defn- normalize-lower [np dp bound value]
  (function/app
   (function/const* 'nnrat/at-most-multiply-left-normalize-lower [])
   np dp bound value))

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

(defn- positive [numerator-predecessor denominator-predecessor]
  (make (succ numerator-predecessor) denominator-predecessor))
(defn- matching-target [b c x]
  (divide (multiply c x) b))
(defn- dual-lower [a c]
  (divide c a))
(defn- matching-lowers [a c]
  (cons-nnrat (dual-lower a c) (nil-nnrat)))
(defn- matching-system [a b c x]
  (chain-solvable (nil-layer)
                  (matching-lowers a c)
                  (matching-target b c x)
                  (nil-nnrat)))
(defn- matching-dual [a b c x]
  (proposition/existence
   type-level nnrat
   (function/lam
    [['y nnrat]]
    (proposition/conjunction
     (dual-feasible a c 'y)
     (gap b c x 'y)))))

;; Scalar weak duality is the algebraic certificate used by both optimality
;; directions below.
(def scalar-weak-duality-spec
  {:name 'nnrat/lp-single-constraint-weak-duality
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]]
    (at-most (multiply 'c 'x) (multiply 'b 'y)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]]
    (let [cx (multiply 'c 'x)
          ayx (multiply (multiply 'a 'y) 'x)
          axy (multiply (multiply 'a 'x) 'y)
          by (multiply 'b 'y)
          first (multiply-right-monotone
                 'c (multiply 'a 'y) 'x 'hd)
          swap (multiply-swap-right 'a 'y 'x)
          first-normalized
          (at-most-respects
           cx cx axy ayx
           (equivalent-reflexive cx)
           (equivalent-symmetric ayx axy swap)
           first)
          second (multiply-right-monotone
                  (multiply 'a 'x) 'b 'y 'hp)]
      (at-most-transitive cx axy by first-normalized second)))})

(def primal-optimality-spec
  {:name 'nnrat/lp-single-constraint-optimality-certificate
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]
     ['hgap (gap 'b 'c 'x 'y)]]
    (primal-optimal 'a 'b 'c 'x))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]
     ['hgap (gap 'b 'c 'x 'y)]
     ['x-alt nnrat] ['hp-alt (primal-feasible 'a 'b 'x-alt)]]
    (let [cx-alt (multiply 'c 'x-alt)
          cx (multiply 'c 'x)
          by (multiply 'b 'y)
          weak
          (function/app
           (function/const* 'nnrat/lp-single-constraint-weak-duality [])
           'a 'b 'c 'x-alt 'y 'hp-alt 'hd)]
      (at-most-respects
       cx-alt cx-alt cx by
       (equivalent-reflexive cx-alt) 'hgap weak)))})

(def dual-optimality-spec
  {:name 'nnrat/lp-single-constraint-dual-optimality-certificate
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]
     ['hgap (gap 'b 'c 'x 'y)]]
    (dual-optimal 'a 'b 'c 'y))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['x nnrat] ['y nnrat]
     ['hp (primal-feasible 'a 'b 'x)]
     ['hd (dual-feasible 'a 'c 'y)]
     ['hgap (gap 'b 'c 'x 'y)]
     ['y-alt nnrat] ['hd-alt (dual-feasible 'a 'c 'y-alt)]]
    (let [cx (multiply 'c 'x)
          by (multiply 'b 'y)
          by-alt (multiply 'b 'y-alt)
          weak
          (function/app
           (function/const* 'nnrat/lp-single-constraint-weak-duality [])
           'a 'b 'c 'x 'y-alt 'hp 'hd-alt)]
      (at-most-respects
       by cx by-alt by-alt
       (equivalent-symmetric cx by 'hgap)
       (equivalent-reflexive by-alt)
       weak)))})

;; A matching dual is normalized into the empty-layer chain interval
;; c/a <= y <= (c*x)/b.  Positivity of a and b is structural.
(def matching-dual-encodes-spec
  {:name 'nnrat/lp-single-positive-constraint-dual-match-encodes
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['matching
      (matching-dual (positive 'ap 'adp) (positive 'bp 'bdp) 'c 'x)]]
    (matching-system (positive 'ap 'adp) (positive 'bp 'bdp) 'c 'x))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['matching
      (matching-dual (positive 'ap 'adp) (positive 'bp 'bdp) 'c 'x)]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          cx (multiply 'c 'x)
          target (matching-target b 'c 'x)
          lower (dual-lower a 'c)
          lowers (matching-lowers a 'c)
          predicate
          (function/lam
           [['y nnrat]]
           (proposition/conjunction
            (dual-feasible a 'c 'y)
            (gap b 'c 'x 'y)))
          result (matching-system a b 'c 'x)]
      (use-witness
       predicate result 'matching
       (function/lam
        [['y nnrat]
         ['evidence
          (proposition/conjunction
           (dual-feasible a 'c 'y)
           (gap b 'c 'x 'y))]]
        (let [hd
              (left-conjunct (dual-feasible a 'c 'y)
                             (gap b 'c 'x 'y) 'evidence)
              hgap
              (right-conjunct (dual-feasible a 'c 'y)
                              (gap b 'c 'x 'y) 'evidence)
              lower-order
              (equivalence-forward
               (dual-feasible a 'c 'y)
               (at-most lower 'y)
               (normalize-lower 'ap 'adp 'c 'y)
               hd)
              by (multiply b 'y)
              by-at-most-cx
              (at-most-respects
               by cx cx cx
               (equivalent-symmetric cx by hgap)
               (equivalent-reflexive cx)
               (at-most-reflexive cx))
              upper-order
              (equivalence-forward
               (at-most by cx) (at-most 'y target)
               (normalize-upper 'bp 'bdp 'y cx)
               by-at-most-cx)
              lower-proof
              (conjoin (at-most lower 'y) (proposition/truth)
                       lower-order
                       (function/const* 'proposition/trivial []))
              upper-proof
              (conjoin (at-most 'y target) (proposition/truth)
                       upper-order
                       (function/const* 'proposition/trivial []))
              open-proof
              (function/app (function/const* 'nnrat/zero-at-most []) 'y)
              upper-open
              (conjoin (le-all target (nil-nnrat) 'y)
                       (chain-open-solvable (nil-layer) 'y)
                       upper-proof open-proof)
              all-evidence
              (conjoin (ge-all lowers 'y)
                       (proposition/conjunction
                        (le-all target (nil-nnrat) 'y)
                        (chain-open-solvable (nil-layer) 'y))
                       lower-proof upper-open)
              chain-predicate
              (function/lam
               [['survivor nnrat]]
               (proposition/conjunction
                (ge-all lowers 'survivor)
                (proposition/conjunction
                 (le-all target (nil-nnrat) 'survivor)
                 (chain-open-solvable (nil-layer) 'survivor))))]
          (witness chain-predicate 'y all-evidence))))))})

;; Conversely, the interval witness proves that the upper endpoint itself is
;; dual feasible.  Choosing that endpoint makes the objective equality exact up
;; to nnrat equivalence, and scalar weak duality supplies optimality.
(def matching-dual-extracts-spec
  {:name 'nnrat/lp-single-positive-constraint-dual-match-extracts
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['hp (primal-feasible (positive 'ap 'adp)
                           (positive 'bp 'bdp) 'x)]
     ['solution
      (matching-system (positive 'ap 'adp)
                       (positive 'bp 'bdp) 'c 'x)]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['y nnrat]]
      (proposition/conjunction
       (dual-feasible (positive 'ap 'adp) 'c 'y)
       (proposition/conjunction
        (gap (positive 'bp 'bdp) 'c 'x 'y)
        (primal-optimal (positive 'ap 'adp)
                        (positive 'bp 'bdp) 'c 'x))))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['hp (primal-feasible (positive 'ap 'adp)
                           (positive 'bp 'bdp) 'x)]
     ['solution
      (matching-system (positive 'ap 'adp)
                       (positive 'bp 'bdp) 'c 'x)]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          cx (multiply 'c 'x)
          target (matching-target b 'c 'x)
          lower (dual-lower a 'c)
          lowers (matching-lowers a 'c)
          chain-predicate
          (function/lam
           [['survivor nnrat]]
           (proposition/conjunction
            (ge-all lowers 'survivor)
            (proposition/conjunction
             (le-all target (nil-nnrat) 'survivor)
             (chain-open-solvable (nil-layer) 'survivor))))
          result
          (proposition/existence
           type-level nnrat
           (function/lam
            [['y nnrat]]
            (proposition/conjunction
             (dual-feasible a 'c 'y)
             (proposition/conjunction
              (gap b 'c 'x 'y)
              (primal-optimal a b 'c 'x)))))]
      (use-witness
       chain-predicate result 'solution
       (function/lam
        [['survivor nnrat]
         ['evidence
          (proposition/conjunction
           (ge-all lowers 'survivor)
           (proposition/conjunction
            (le-all target (nil-nnrat) 'survivor)
            (chain-open-solvable (nil-layer) 'survivor)))]]
        (let [tail-prop
              (proposition/conjunction
               (le-all target (nil-nnrat) 'survivor)
               (chain-open-solvable (nil-layer) 'survivor))
              lower-all
              (left-conjunct (ge-all lowers 'survivor)
                             tail-prop 'evidence)
              tail
              (right-conjunct (ge-all lowers 'survivor)
                              tail-prop 'evidence)
              upper-all
              (left-conjunct (le-all target (nil-nnrat) 'survivor)
                             (chain-open-solvable (nil-layer) 'survivor)
                             tail)
              lower-order
              (left-conjunct (at-most lower 'survivor)
                             (proposition/truth) lower-all)
              upper-order
              (left-conjunct (at-most 'survivor target)
                             (proposition/truth) upper-all)
              lower-at-most-target
              (at-most-transitive lower 'survivor target
                                  lower-order upper-order)
              hd
              (equivalence-backward
               (dual-feasible a 'c target)
               (at-most lower target)
               (normalize-lower 'ap 'adp 'c target)
               lower-at-most-target)
              cancel-b (multiply-divide-cancel 'bp 'bdp cx)
              hgap
              (equivalent-symmetric (multiply b target) cx cancel-b)
              optimal
              (function/app
               (function/const*
                'nnrat/lp-single-constraint-optimality-certificate [])
               a b 'c 'x target 'hp hd hgap)
              gap-optimal
              (conjoin (gap b 'c 'x target)
                       (primal-optimal a b 'c 'x)
                       hgap optimal)
              all
              (conjoin (dual-feasible a 'c target)
                       (proposition/conjunction
                        (gap b 'c 'x target)
                        (primal-optimal a b 'c 'x))
                       hd gap-optimal)
              output-predicate
              (function/lam
               [['y nnrat]]
               (proposition/conjunction
                (dual-feasible a 'c 'y)
                (proposition/conjunction
                 (gap b 'c 'x 'y)
                 (primal-optimal a b 'c 'x))))]
          (witness output-predicate target all))))))})

(def matching-encoding-iff-spec
  {:name 'nnrat/lp-single-positive-constraint-dual-match-encoding-iff
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]]
    (proposition/equivalence
     (matching-dual (positive 'ap 'adp) (positive 'bp 'bdp) 'c 'x)
     (matching-system (positive 'ap 'adp) (positive 'bp 'bdp) 'c 'x)))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          left (matching-dual a b 'c 'x)
          right (matching-system a b 'c 'x)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       left right
       (function/lam
        [['matching left]]
        (function/app
         (function/const*
          'nnrat/lp-single-positive-constraint-dual-match-encodes [])
         'ap 'adp 'bp 'bdp 'c 'x 'matching))
       (function/lam
        [['solution right]]
        (let [target (matching-target b 'c 'x)
                lower (dual-lower a 'c)
                lowers (matching-lowers a 'c)
                chain-predicate
                (function/lam
                 [['survivor nnrat]]
                 (proposition/conjunction
                  (ge-all lowers 'survivor)
                  (proposition/conjunction
                   (le-all target (nil-nnrat) 'survivor)
                   (chain-open-solvable (nil-layer) 'survivor))))]
            (use-witness
             chain-predicate left 'solution
             (function/lam
              [['survivor nnrat]
               ['evidence
                (proposition/conjunction
                 (ge-all lowers 'survivor)
                 (proposition/conjunction
                  (le-all target (nil-nnrat) 'survivor)
                  (chain-open-solvable (nil-layer) 'survivor)))]]
              (let [tail-prop
                    (proposition/conjunction
                     (le-all target (nil-nnrat) 'survivor)
                     (chain-open-solvable (nil-layer) 'survivor))
                    lower-all
                    (left-conjunct (ge-all lowers 'survivor)
                                   tail-prop 'evidence)
                    tail
                    (right-conjunct (ge-all lowers 'survivor)
                                    tail-prop 'evidence)
                    upper-all
                    (left-conjunct
                     (le-all target (nil-nnrat) 'survivor)
                     (chain-open-solvable (nil-layer) 'survivor)
                     tail)
                    lower-order
                    (left-conjunct (at-most lower 'survivor)
                                   (proposition/truth) lower-all)
                    upper-order
                    (left-conjunct (at-most 'survivor target)
                                   (proposition/truth) upper-all)
                    lower-target
                    (at-most-transitive lower 'survivor target
                                        lower-order upper-order)
                    hd
                    (equivalence-backward
                     (dual-feasible a 'c target)
                     (at-most lower target)
                     (normalize-lower 'ap 'adp 'c target)
                     lower-target)
                    cancel-b
                    (multiply-divide-cancel 'bp 'bdp (multiply 'c 'x))
                    hgap
                    (equivalent-symmetric
                     (multiply b target) (multiply 'c 'x) cancel-b)
                    pair
                    (conjoin (dual-feasible a 'c target)
                             (gap b 'c 'x target) hd hgap)
                    predicate
                    (function/lam
                     [['y nnrat]]
                     (proposition/conjunction
                      (dual-feasible a 'c 'y)
                      (gap b 'c 'x 'y)))]
                (witness predicate target pair)))))))))})

(def strong-duality-or-certificate-spec
  {:name 'nnrat/lp-single-positive-constraint-strong-duality-or-farkas-certificate
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['hp (primal-feasible (positive 'ap 'adp)
                           (positive 'bp 'bdp) 'x)]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          system (matching-system a b 'c 'x)
          matching (matching-dual a b 'c 'x)
          success
          (proposition/existence
           type-level nnrat
           (function/lam
            [['y nnrat]]
            (proposition/conjunction
             (dual-feasible a 'c 'y)
             (proposition/conjunction
              (gap b 'c 'x 'y)
              (primal-optimal a b 'c 'x)))))]
      (proposition/disjunction
       success
       (proposition/conjunction
        (proposition/negation matching)
        (proposition/negation system)))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat]
     ['c nnrat] ['x nnrat]
     ['hp (primal-feasible (positive 'ap 'adp)
                           (positive 'bp 'bdp) 'x)]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          system (matching-system a b 'c 'x)
          matching (matching-dual a b 'c 'x)
          success
          (proposition/existence
           type-level nnrat
           (function/lam
            [['y nnrat]]
            (proposition/conjunction
             (dual-feasible a 'c 'y)
             (proposition/conjunction
              (gap b 'c 'x 'y)
              (primal-optimal a b 'c 'x)))))
          failure
          (proposition/conjunction
           (proposition/negation matching)
           (proposition/negation system))
          result (proposition/disjunction success failure)
          decision
          (function/app
           (function/const* 'nnrat/farkas-elim-chain-solvable-or-not [])
           (nil-layer) (matching-lowers a 'c)
           (matching-target b 'c 'x) (nil-nnrat))]
      (use-disjunction
       system (proposition/negation system) result decision
       (function/lam
        [['solution system]]
        (left-disjunct
         success failure
         (function/app
          (function/const*
           'nnrat/lp-single-positive-constraint-dual-match-extracts [])
          'ap 'adp 'bp 'bdp 'c 'x 'hp 'solution)))
       (function/lam
        [['not-system (proposition/negation system)]]
        (let [not-matching
              (function/lam
               [['matching-proof matching]]
               (function/app
                'not-system
                (function/app
                 (function/const*
                  'nnrat/lp-single-positive-constraint-dual-match-encodes [])
                 'ap 'adp 'bp 'bdp 'c 'x 'matching-proof)))
              certificate
              (conjoin (proposition/negation matching)
                       (proposition/negation system)
                       not-matching 'not-system)]
          (right-disjunct success failure certificate))))))})

(def scalar-strong-duality-spec
  {:name 'nnrat/lp-single-positive-constraint-strong-duality
   :universes []
   :type
   (function/forall
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat] ['c nnrat]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          x (divide b a)
          y (divide 'c a)]
      (proposition/conjunction
       (primal-feasible a b x)
       (proposition/conjunction
        (dual-feasible a 'c y)
        (proposition/conjunction
         (gap b 'c x y)
         (proposition/conjunction
          (primal-optimal a b 'c x)
          (proposition/conjunction
           (dual-optimal a b 'c y)
           (matching-system a b 'c x))))))))
   :value
   (function/lam
    [['ap nat] ['adp nat] ['bp nat] ['bdp nat] ['c nnrat]]
    (let [a (positive 'ap 'adp)
          b (positive 'bp 'bdp)
          x (divide b a)
          y (divide 'c a)
          ax (multiply a x)
          ay (multiply a y)
          cx (multiply 'c x)
          by (multiply b y)
          cancel-a-b (multiply-divide-cancel 'ap 'adp b)
          cancel-a-c (multiply-divide-cancel 'ap 'adp 'c)
          hp
          (at-most-respects
           ax b b b cancel-a-b (equivalent-reflexive b)
           (at-most-reflexive b))
          hd
          (at-most-respects
           'c 'c ay 'c
           (equivalent-reflexive 'c) cancel-a-c
           (at-most-reflexive 'c))
          c-to-ay
          (equivalent-symmetric ay 'c cancel-a-c)
          first
          (multiply-respects
           'c ay x x c-to-ay (equivalent-reflexive x))
          swapped (multiply-swap-right a y x)
          replace-ax
          (multiply-respects
           ax b y y cancel-a-b (equivalent-reflexive y))
          through-swap
          (equivalent-transitive cx (multiply ay x)
                                 (multiply ax y) first swapped)
          hgap
          (equivalent-transitive cx (multiply ax y) by
                                 through-swap replace-ax)
          primal-optimal-proof
          (function/app
           (function/const*
            'nnrat/lp-single-constraint-optimality-certificate [])
           a b 'c x y hp hd hgap)
          dual-optimal-proof
          (function/app
           (function/const*
            'nnrat/lp-single-constraint-dual-optimality-certificate [])
           a b 'c x y hp hd hgap)
          matching-pair
          (witness
           (function/lam
            [['candidate nnrat]]
            (proposition/conjunction
             (dual-feasible a 'c 'candidate)
             (gap b 'c x 'candidate)))
           y
           (conjoin (dual-feasible a 'c y) (gap b 'c x y) hd hgap))
          system-proof
          (function/app
           (function/const*
            'nnrat/lp-single-positive-constraint-dual-match-encodes [])
           'ap 'adp 'bp 'bdp 'c x matching-pair)
          dual-and-system
          (conjoin (dual-optimal a b 'c y)
                   (matching-system a b 'c x)
                   dual-optimal-proof system-proof)
          optimal-tail
          (conjoin (primal-optimal a b 'c x)
                   (proposition/conjunction
                    (dual-optimal a b 'c y)
                    (matching-system a b 'c x))
                   primal-optimal-proof dual-and-system)
          gap-tail
          (conjoin (gap b 'c x y)
                   (proposition/conjunction
                    (primal-optimal a b 'c x)
                    (proposition/conjunction
                     (dual-optimal a b 'c y)
                     (matching-system a b 'c x)))
                   hgap optimal-tail)
          dual-tail
          (conjoin (dual-feasible a 'c y)
                   (proposition/conjunction
                    (gap b 'c x y)
                    (proposition/conjunction
                     (primal-optimal a b 'c x)
                     (proposition/conjunction
                      (dual-optimal a b 'c y)
                      (matching-system a b 'c x))))
                   hd gap-tail)]
      (conjoin
       (primal-feasible a b x)
       (proposition/conjunction
        (dual-feasible a 'c y)
        (proposition/conjunction
         (gap b 'c x y)
         (proposition/conjunction
          (primal-optimal a b 'c x)
          (proposition/conjunction
           (dual-optimal a b 'c y)
           (matching-system a b 'c x)))))
       hp dual-tail)))})

(def definition-specs [])

(def theorem-specs
  [scalar-weak-duality-spec
   primal-optimality-spec
   dual-optimality-spec
   matching-dual-encodes-spec
   matching-dual-extracts-spec
   matching-encoding-iff-spec
   strong-duality-or-certificate-spec
   scalar-strong-duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      alternative/extend-environment
      scale/extend-environment
      right-monotone/extend-environment
      (support/extend-with :nnrat-lp-strong-duality-general theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
