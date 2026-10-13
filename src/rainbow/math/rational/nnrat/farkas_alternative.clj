(ns rainbow.math.rational.nnrat.farkas-alternative
  "Constructive Farkas alternative for arbitrary finite nnrat elimination chains.

  The executable cross-product comparison decides each scalar order atom.  Its
  decisions are lifted through the upper-bound lists and the finite elimination
  layers, making the collapsed Fourier--Motzkin condition decidable.  Transport
  through `farkas-elim-chain-solvable-iff` then gives the named alternative:
  every chain is either solvable or provably not solvable.  The negative branch
  is a checkable Farkas certificate: a refutation of the collapsed reduced
  condition.  All declarations are native proof data and axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-chain :as elim-chain]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nat-successor (function/const* 'data/succ []))
(def nat-one (function/app nat-successor nat-zero))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

;; A chain layer is (lowers, (upper-head, upper-tail)), matching the elimination
;; engine's public data representation.
(def upper-family
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat list-nnrat))
(def layer
  (function/app (function/const* 'data/Product [type-level type-level])
                list-nnrat upper-family))
(def list-layer
  (function/app (function/const* 'data/List [type-level]) layer))

(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- layer-lowers [entry]
  (first-of list-nnrat upper-family entry))
(defn- layer-upper-family [entry]
  (second-of list-nnrat upper-family entry))
(defn- layer-u0 [entry]
  (first-of nnrat list-nnrat (layer-upper-family entry)))
(defn- layer-urest [entry]
  (second-of nnrat list-nnrat (layer-upper-family entry)))

(defn- nil-of [carrier]
  (function/app (function/const* 'data/nil [type-level]) carrier))
(defn- cons-of [carrier head tail]
  (function/app (function/const* 'data/cons [type-level]) carrier head tail))
(defn- nil-nnrat [] (nil-of nnrat))
(defn- nil-layer [] (nil-of layer))
(defn- cons-nnrat [head tail] (cons-of nnrat head tail))

(defn- nat-add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- nat-at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))
(defn- nat-decide-at-most [left right]
  (function/app (function/const* 'nat/decide-at-most []) left right))
(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- list-reduced [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-reduced [])
                lowers u0 urest))
(defn- chain-lower [layers]
  (function/app (function/const* 'nnrat/farkas-elim-chain-lower []) layers))
(defn- chain-feasible [layers]
  (function/app (function/const* 'nnrat/farkas-elim-chain-feasible []) layers))
(defn- reduced [layers terminal-lowers terminal-u0 terminal-urest]
  (function/app (function/const* 'nnrat/farkas-elim-chain-reduced [])
                layers terminal-lowers terminal-u0 terminal-urest))
(defn- solvable [layers terminal-lowers terminal-u0 terminal-urest]
  (function/app (function/const* 'nnrat/farkas-elim-chain-solvable [])
                layers terminal-lowers terminal-u0 terminal-urest))

(defn- decidable [claim]
  (proposition/disjunction claim (proposition/negation claim)))
(defn- eq [carrier left right]
  (function/equality type-level carrier left right))
(defn- reflexive [carrier value]
  (function/app (function/const* 'equality/reflexive [type-level])
                carrier value))
(defn- symmetric [carrier left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                carrier left right same))
(defn- transitive [carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                carrier left middle right first second))
(defn- explode [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))
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
(defn- witness-nat [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nat predicate value evidence))
(defn- use-witness-nat [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nat predicate result evidence continue))
(defn- witness-nnrat [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat predicate value evidence))

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

;; Constructive closure of decidability under conjunction.  The negative cases
;; refute a concrete conjunct extracted from the supplied conjunction evidence.
(defn- conjunction-decision
  [left right left-decision right-decision]
  (let [both (proposition/conjunction left right)
        not-left (proposition/negation left)
        not-right (proposition/negation right)
        target (decidable both)]
    (use-disjunction
     left not-left target left-decision
     (function/lam
      [['left-proof left]]
      (use-disjunction
       right not-right target right-decision
       (function/lam
        [['right-proof right]]
        (left-disjunct both (proposition/negation both)
                       (conjoin left right 'left-proof 'right-proof)))
       (function/lam
        [['not-right-proof not-right]]
        (right-disjunct
         both (proposition/negation both)
         (function/lam
          [['both-proof both]]
          (function/app
           'not-right-proof
           (right-conjunct left right 'both-proof)))))))
     (function/lam
      [['not-left-proof not-left]]
      (right-disjunct
       both (proposition/negation both)
       (function/lam
        [['both-proof both]]
        (function/app
         'not-left-proof
         (left-conjunct left right 'both-proof))))))))

;; If the Peano witness says left <= right, the structural comparison computes
;; to true.  This is the completeness half paired with the checkpoint's soundness
;; theorem and is what makes a false comparison a genuine refutation.
(def nat-at-most-decision-complete-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat] ['ordered (nat-at-most 'left 'right)]]
          (eq bool (nat-decide-at-most 'left 'right) true-value)))]
    {:name 'nat/at-most-decision-complete
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat] ['ordered (nat-at-most 'left 'right)]]
      (eq bool (nat-decide-at-most 'left 'right) true-value))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat] ['ignored (nat-at-most nat-zero 'right)]]
        (reflexive bool true-value))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/forall
           [['ordered
             (nat-at-most (function/app nat-successor 'left-previous)
                          'candidate)]]
           (eq bool
               (nat-decide-at-most
                (function/app nat-successor 'left-previous) 'candidate)
               true-value)))
         (function/lam
          [['ordered
            (nat-at-most (function/app nat-successor 'left-previous)
                         nat-zero)]]
          (let [predicate
                (function/lam
                 [['extra nat]]
                 (eq nat
                     (nat-add (function/app nat-successor 'left-previous)
                              'extra)
                     nat-zero))
                result
                (eq bool
                    (nat-decide-at-most
                     (function/app nat-successor 'left-previous) nat-zero)
                    true-value)]
            (use-witness-nat
             predicate result 'ordered
             (function/lam
              [['extra nat]
               ['same
                (eq nat
                    (nat-add (function/app nat-successor 'left-previous)
                             'extra)
                    nat-zero)]]
              (explode
               result
               (function/app
                (function/const* 'nat/zero-not-successor [])
                (nat-add 'left-previous 'extra)
                (symmetric
                 nat
                 (function/app nat-successor
                               (nat-add 'left-previous 'extra))
                 nat-zero 'same)))))))
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['ordered
               (nat-at-most (function/app nat-successor 'left-previous)
                            'right-previous)]]
             (eq bool
                 (nat-decide-at-most
                  (function/app nat-successor 'left-previous)
                  'right-previous)
                 true-value))]
           ['ordered
            (nat-at-most (function/app nat-successor 'left-previous)
                         (function/app nat-successor 'right-previous))]]
          (let [predecessor-predicate
                (function/lam
                 [['extra nat]]
                 (eq nat (nat-add 'left-previous 'extra) 'right-previous))
                predecessor-order
                (use-witness-nat
                 (function/lam
                  [['extra nat]]
                  (eq nat
                      (nat-add (function/app nat-successor 'left-previous)
                               'extra)
                      (function/app nat-successor 'right-previous)))
                 (nat-at-most 'left-previous 'right-previous)
                 'ordered
                 (function/lam
                  [['extra nat]
                   ['same
                    (eq nat
                        (nat-add
                         (function/app nat-successor 'left-previous) 'extra)
                        (function/app nat-successor 'right-previous))]]
                  (witness-nat
                   predecessor-predicate 'extra
                   (function/app
                    (function/const* 'nat/successor-injective [])
                    (nat-add 'left-previous 'extra) 'right-previous 'same))))]
            (function/app 'induction-hypothesis
                          'right-previous predecessor-order)))
         'right))
       'left))}))

(def nnrat-at-most-decidable-spec
  {:name 'nnrat/at-most-decidable
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]]
    (decidable (at-most 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [claim (at-most 'left 'right)
          not-claim (proposition/negation claim)
          decision (decide-at-most 'left 'right)
          motive
          (function/lam
           [['choice bool]]
           (function/arrow
            (eq bool decision 'choice)
            (decidable claim)))]
      (function/app
       (function/app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        (function/lam
         [['same-false (eq bool decision false-value)]]
         (right-disjunct
          claim not-claim
          (function/lam
           [['ordered claim]]
           (let [cross
                 (function/app
                  (function/const* 'nnrat/at-most-to-cross [])
                  'left 'right 'ordered)
                 complete
                 (function/app
                  (function/const* 'nat/at-most-decision-complete [])
                  (function/app
                   (function/const* 'nat/multiply [])
                   (function/app (function/const* 'nnrat/numerator []) 'left)
                   (function/app (function/const* 'nnrat/denominator []) 'right))
                  (function/app
                   (function/const* 'nat/multiply [])
                   (function/app (function/const* 'nnrat/numerator []) 'right)
                   (function/app (function/const* 'nnrat/denominator []) 'left))
                  cross)
                 false-to-decision
                 (symmetric bool decision false-value 'same-false)
                 false-is-true
                 (transitive bool false-value decision true-value
                             false-to-decision complete)]
             (function/app
              (function/const* 'bool/false-not-true []) false-is-true)))))
        (function/lam
         [['same-true (eq bool decision true-value)]]
         (left-disjunct
          claim not-claim
          (function/app
           (function/const* 'nnrat/decide-at-most-true-sound [])
           'left 'right 'same-true)))
        decision)
       (reflexive bool decision))))})

(def upper-rest-decidable-spec
  (let [motive
        (function/lam
         [['ys list-nnrat]]
         (function/forall
          [['value nnrat]]
          (decidable (upper-rest 'ys 'value))))]
    {:name 'nnrat/farkas-upper-rest-decidable
     :universes []
     :type
     (function/forall
      [['urest list-nnrat] ['value nnrat]]
      (decidable (upper-rest 'urest 'value)))
     :value
     (function/lam
      [['urest list-nnrat]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       nnrat motive
       (function/lam
        [['value nnrat]]
        (left-disjunct
         (proposition/truth)
         (proposition/negation (proposition/truth))
         (function/const* 'proposition/trivial [])))
       (function/lam
        [['upper nnrat] ['tail list-nnrat]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value nnrat]]
        (conjunction-decision
         (at-most 'value 'upper)
         (upper-rest 'tail 'value)
         (function/app (function/const* 'nnrat/at-most-decidable [])
                       'value 'upper)
         (function/app 'induction-hypothesis 'value)))
       'urest))}))

(def le-all-decidable-spec
  {:name 'nnrat/le-all-decidable
   :universes []
   :type
   (function/forall
    [['u0 nnrat] ['urest list-nnrat] ['value nnrat]]
    (decidable (le-all 'u0 'urest 'value)))
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['value nnrat]]
    (conjunction-decision
     (at-most 'value 'u0)
     (upper-rest 'urest 'value)
     (function/app (function/const* 'nnrat/at-most-decidable [])
                   'value 'u0)
     (function/app (function/const* 'nnrat/farkas-upper-rest-decidable [])
                   'urest 'value)))})

(def list-reduced-decidable-spec
  {:name 'nnrat/farkas-elim-list-reduced-decidable
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (decidable (list-reduced 'lowers 'u0 'urest)))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]]
    (function/app (function/const* 'nnrat/le-all-decidable [])
                  'u0 'urest (max-lb 'lowers)))})

(def chain-feasible-decidable-spec
  (let [motive
        (function/lam
         [['ys list-layer]]
         (decidable (chain-feasible 'ys)))]
    {:name 'nnrat/farkas-elim-chain-feasible-decidable
     :universes []
     :type
     (function/forall
      [['layers list-layer]]
      (decidable (chain-feasible 'layers)))
     :value
     (function/lam
      [['layers list-layer]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       layer motive
       (left-disjunct
        (proposition/truth)
        (proposition/negation (proposition/truth))
        (function/const* 'proposition/trivial []))
       (function/lam
        [['entry layer] ['tail list-layer]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [augmented
              (cons-nnrat (chain-lower 'tail) (layer-lowers 'entry))
              layer-condition
              (list-reduced augmented
                            (layer-u0 'entry) (layer-urest 'entry))]
          (conjunction-decision
           (chain-feasible 'tail) layer-condition
           'induction-hypothesis
           (function/app
            (function/const* 'nnrat/farkas-elim-list-reduced-decidable [])
            augmented (layer-u0 'entry) (layer-urest 'entry)))))
       'layers))}))

(def chain-reduced-decidable-spec
  {:name 'nnrat/farkas-elim-chain-reduced-decidable
   :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (decidable
     (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (let [final-lowers
          (cons-nnrat (chain-lower 'layers) 'terminal-lowers)
          final-condition
          (list-reduced final-lowers 'terminal-u0 'terminal-urest)]
      (conjunction-decision
       (chain-feasible 'layers) final-condition
       (function/app
        (function/const* 'nnrat/farkas-elim-chain-feasible-decidable [])
        'layers)
       (function/app
        (function/const* 'nnrat/farkas-elim-list-reduced-decidable [])
        final-lowers 'terminal-u0 'terminal-urest))))})

(def chain-infeasibility-certificate-spec
  {:name 'nnrat/farkas-elim-chain-infeasibility-certificate
   :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['not-reduced
      (proposition/negation
       (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest))]]
    (proposition/negation
     (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['not-reduced
      (proposition/negation
       (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest))]
     ['solution
      (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]]
    (function/app
     'not-reduced
     (function/app
      (function/const* 'nnrat/farkas-elim-chain-projects [])
      'layers 'terminal-lowers 'terminal-u0 'terminal-urest 'solution)))})

(def chain-solvable-or-not-spec
  {:name 'nnrat/farkas-elim-chain-solvable-or-not
   :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (decidable
     (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (let [reduced-prop
          (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)
          solvable-prop
          (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)
          not-reduced (proposition/negation reduced-prop)
          not-solvable (proposition/negation solvable-prop)
          target (decidable solvable-prop)]
      (use-disjunction
       reduced-prop not-reduced target
       (function/app
        (function/const* 'nnrat/farkas-elim-chain-reduced-decidable [])
        'layers 'terminal-lowers 'terminal-u0 'terminal-urest)
       (function/lam
        [['reduced-proof reduced-prop]]
        (left-disjunct
         solvable-prop not-solvable
         (function/app
          (function/const* 'nnrat/farkas-elim-chain-extends [])
          'layers 'terminal-lowers 'terminal-u0 'terminal-urest
          'reduced-proof)))
       (function/lam
        [['not-reduced-proof not-reduced]]
        (right-disjunct
         solvable-prop not-solvable
         (function/app
          (function/const*
           'nnrat/farkas-elim-chain-infeasibility-certificate [])
          'layers 'terminal-lowers 'terminal-u0 'terminal-urest
          'not-reduced-proof))))))})

;; Two closed instances witness that the alternative is not vacuous.  The first
;; has no layers or extra terminal lowers and is solved by zero.
(def zero-instance-solvable-spec
  (let [layers (nil-layer)
        lowers (nil-nnrat)
        uppers (nil-nnrat)
        upper-prop (le-all nnrat-zero uppers nnrat-zero)
        open-prop
        (function/app (function/const* 'nnrat/farkas-elim-chain-open-solvable [])
                      layers nnrat-zero)
        predicate
        (function/lam
         [['value nnrat]]
         (proposition/conjunction
          (ge-all lowers 'value)
          (proposition/conjunction
           (le-all nnrat-zero uppers 'value)
           (function/app
            (function/const* 'nnrat/farkas-elim-chain-open-solvable [])
            layers 'value))))]
    {:name 'nnrat/farkas-elim-chain-zero-instance-solvable
     :universes []
     :type (solvable layers lowers nnrat-zero uppers)
     :value
     (let [refl (function/app (function/const* 'nnrat/at-most-reflexive [])
                              nnrat-zero)
           upper-proof
           (conjoin (at-most nnrat-zero nnrat-zero)
                    (proposition/truth)
                    refl (function/const* 'proposition/trivial []))
           upper-open-proof
           (conjoin upper-prop open-prop upper-proof refl)
           evidence
           (conjoin
            (proposition/truth)
            (proposition/conjunction upper-prop open-prop)
            (function/const* 'proposition/trivial [])
            upper-open-proof)]
       (witness-nnrat predicate nnrat-zero evidence))}))

;; The second asks a terminal survivor to be at least one and at most zero.
;; Its refutation extracts 1 <= max-lb <= 0 and reduces that impossible order
;; to the Peano contradiction 0 = successor(extra).
(def unit-zero-instance-not-reduced-spec
  (let [layers (nil-layer)
        terminal-lowers (cons-nnrat nnrat-one (nil-nnrat))
        terminal-uppers (nil-nnrat)
        reduced-prop
        (reduced layers terminal-lowers nnrat-zero terminal-uppers)
        final-lowers
        (cons-nnrat (chain-lower layers) terminal-lowers)]
    {:name 'nnrat/farkas-elim-chain-unit-zero-instance-not-reduced
     :universes []
     :type (proposition/negation reduced-prop)
     :value
     (function/lam
      [['reduced-proof reduced-prop]]
      (let [final-condition (list-reduced final-lowers
                                          nnrat-zero terminal-uppers)
            final-proof
            (right-conjunct (chain-feasible layers) final-condition
                            'reduced-proof)
            folded (max-lb final-lowers)
            folded-at-most-zero
            (left-conjunct
             (at-most folded nnrat-zero)
             (proposition/truth)
             final-proof)
            all-below-fold (ge-all final-lowers folded)
            all-below-fold-proof
            (function/app (function/const* 'nnrat/max-lb-is-upper [])
                          final-lowers)
            tail-below-fold
            (right-conjunct
             (at-most (chain-lower layers) folded)
             (ge-all terminal-lowers folded)
             all-below-fold-proof)
            one-at-most-folded
            (left-conjunct
             (at-most nnrat-one folded)
             (proposition/truth)
             tail-below-fold)
            one-at-most-zero
            (function/app (function/const* 'nnrat/at-most-transitive [])
                          nnrat-one folded nnrat-zero
                          one-at-most-folded folded-at-most-zero)
            cross
            (function/app (function/const* 'nnrat/at-most-to-cross [])
                          nnrat-one nnrat-zero one-at-most-zero)
            predicate
            (function/lam
             [['extra nat]]
             (eq nat (nat-add nat-one 'extra) nat-zero))]
        (use-witness-nat
         predicate (proposition/falsity) cross
         (function/lam
          [['extra nat]
           ['same (eq nat (nat-add nat-one 'extra) nat-zero)]]
          (function/app
           (function/const* 'nat/zero-not-successor [])
           'extra
           (symmetric nat
                      (function/app nat-successor 'extra)
                      nat-zero 'same))))))}))

(def unit-zero-instance-not-solvable-spec
  (let [layers (nil-layer)
        terminal-lowers (cons-nnrat nnrat-one (nil-nnrat))
        terminal-uppers (nil-nnrat)]
    {:name 'nnrat/farkas-elim-chain-unit-zero-instance-not-solvable
     :universes []
     :type
     (proposition/negation
      (solvable layers terminal-lowers nnrat-zero terminal-uppers))
     :value
     (function/app
      (function/const* 'nnrat/farkas-elim-chain-infeasibility-certificate [])
      layers terminal-lowers nnrat-zero terminal-uppers
      (function/const*
       'nnrat/farkas-elim-chain-unit-zero-instance-not-reduced []))}))

(def definition-specs [])

(def theorem-specs
  [nat-at-most-decision-complete-spec
   nnrat-at-most-decidable-spec
   upper-rest-decidable-spec
   le-all-decidable-spec
   list-reduced-decidable-spec
   chain-feasible-decidable-spec
   chain-reduced-decidable-spec
   chain-infeasibility-certificate-spec
   chain-solvable-or-not-spec
   zero-instance-solvable-spec
   unit-zero-instance-not-reduced-spec
   unit-zero-instance-not-solvable-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-chain rainbow.math.rational.nnrat.order-equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-alternative theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-alternative))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
