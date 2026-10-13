(ns rainbow.math.rational.nnrat.farkas-elim-chain
  "Arbitrary finite chains of constructive nnrat Fourier--Motzkin steps.

  A layer stores constant lower bounds and a non-empty upper family for one
  eliminated variable.  Layers are ordered from the variable nearest the final
  survivor outwards.  The open system nests one witness per layer, with every
  layer variable bounded above by its survivor.  Folding from the tail transfers
  each `max-lb` onto the next variable.  A final list elimination then quantifies
  the survivor, so `farkas-elim-chain-solvable-iff` decides chains of every finite
  length.  All definitions and proofs are native proof data and axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim-list]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as elim-coupled]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

;; A layer is (lowers, (upper-head, upper-tail)).
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

(defn- nil-nnrat []
  (function/app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level])
                nnrat head tail))

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
(defn- list-solvable [lowers u0 urest]
  (function/app (function/const* 'nnrat/farkas-elim-list-solvable [])
                lowers u0 urest))
(defn- coupled-reduced [lowers u0 urest survivor]
  (function/app (function/const* 'nnrat/farkas-elim-coupled-reduced [])
                lowers u0 urest survivor))
(defn- coupled-solvable [lowers u0 urest survivor]
  (function/app (function/const* 'nnrat/farkas-elim-coupled-solvable [])
                lowers u0 urest survivor))

(defn- chain-lower [layers]
  (function/app (function/const* 'nnrat/farkas-elim-chain-lower []) layers))
(defn- chain-feasible [layers]
  (function/app (function/const* 'nnrat/farkas-elim-chain-feasible []) layers))
(defn- open-reduced [layers survivor]
  (function/app (function/const* 'nnrat/farkas-elim-chain-open-reduced [])
                layers survivor))
(defn- open-solvable [layers survivor]
  (function/app (function/const* 'nnrat/farkas-elim-chain-open-solvable [])
                layers survivor))
(defn- reduced [layers terminal-lowers terminal-u0 terminal-urest]
  (function/app (function/const* 'nnrat/farkas-elim-chain-reduced [])
                layers terminal-lowers terminal-u0 terminal-urest))
(defn- solvable [layers terminal-lowers terminal-u0 terminal-urest]
  (function/app (function/const* 'nnrat/farkas-elim-chain-solvable [])
                layers terminal-lowers terminal-u0 terminal-urest))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- witness [predicate value evidence]
  (function/app (function/const* 'proposition/witness [type-level])
                nnrat predicate value evidence))
(defn- use-witness [predicate result evidence continue]
  (function/app (function/const* 'proposition/use-witness [type-level])
                nnrat predicate result evidence continue))

(defn- augmented-lowers [entry tail]
  (cons-nnrat (chain-lower tail) (layer-lowers entry)))

(defn- layer-step-prop [entry tail survivor value]
  (proposition/conjunction
   (ge-all (layer-lowers entry) value)
   (proposition/conjunction
    (le-all (layer-u0 entry) (layer-urest entry) value)
    (proposition/conjunction
     (at-most value survivor)
     (open-solvable tail value)))))

(defn- terminal-step-prop
  [layers terminal-lowers terminal-u0 terminal-urest value]
  (proposition/conjunction
   (ge-all terminal-lowers value)
   (proposition/conjunction
    (le-all terminal-u0 terminal-urest value)
    (open-solvable layers value))))

;; Definitions -------------------------------------------------------------

;; The scalar lower bound propagated by all eliminated variables.  The tail is
;; farther from the final survivor, so its folded lower becomes a new lower in
;; the current layer before that layer is eliminated.
(def chain-lower-spec
  {:name 'nnrat/farkas-elim-chain-lower :kind :definition :universes []
   :type (function/arrow list-layer nnrat)
   :value
   (function/lam
    [['layers list-layer]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     layer
     (function/lam [['ignored list-layer]] nnrat)
     nnrat-zero
     (function/lam
      [['entry layer] ['tail list-layer] ['tail-lower nnrat]]
      (max-lb (cons-nnrat 'tail-lower (layer-lowers 'entry))))
     'layers))})

;; Every eliminated layer must also satisfy its upper family after the lower
;; transferred from the tail is inserted.
(def chain-feasible-spec
  {:name 'nnrat/farkas-elim-chain-feasible :kind :definition :universes []
   :type (function/arrow list-layer 'Prop)
   :value
   (function/lam
    [['layers list-layer]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     layer
     (function/lam [['ignored list-layer]] 'Prop)
     (proposition/truth)
     (function/lam
      [['entry layer] ['tail list-layer] ['tail-feasible 'Prop]]
      (proposition/conjunction
       'tail-feasible
       (list-reduced (augmented-lowers 'entry 'tail)
                     (layer-u0 'entry) (layer-urest 'entry))))
     'layers))})

(def open-reduced-spec
  {:name 'nnrat/farkas-elim-chain-open-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-layer nnrat 'Prop)
   :value
   (function/lam
    [['layers list-layer] ['survivor nnrat]]
    (proposition/conjunction
     (chain-feasible 'layers)
     (at-most (chain-lower 'layers) 'survivor)))})

;; The empty chain contributes only the native zero lower bound.  A cons adds
;; one witness whose upper survivor is followed by the recursively nested tail.
(def open-solvable-spec
  {:name 'nnrat/farkas-elim-chain-open-solvable
   :kind :definition
   :universes []
   :type (function/arrow list-layer nnrat 'Prop)
   :value
   (function/lam
    [['layers list-layer] ['survivor nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     layer
     (function/lam [['ignored list-layer]] (function/arrow nnrat 'Prop))
     (function/lam [['value nnrat]] (at-most nnrat-zero 'value))
     (function/lam
      [['entry layer] ['tail list-layer]
       ['tail-solvable (function/arrow nnrat 'Prop)]]
      (function/lam
       [['value nnrat]]
       (proposition/existence
        type-level nnrat
        (function/lam
         [['candidate nnrat]]
         (proposition/conjunction
          (ge-all (layer-lowers 'entry) 'candidate)
          (proposition/conjunction
           (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
           (proposition/conjunction
            (at-most 'candidate 'value)
            (function/app 'tail-solvable 'candidate))))))))
     'layers 'survivor))})

(def reduced-spec
  {:name 'nnrat/farkas-elim-chain-reduced :kind :definition :universes []
   :type (function/arrow list-layer list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (proposition/conjunction
     (chain-feasible 'layers)
     (list-reduced
      (cons-nnrat (chain-lower 'layers) 'terminal-lowers)
      'terminal-u0 'terminal-urest)))})

;; This closes the chain with an existential final survivor.  Its predicate is
;; followed definitionally by the nested existential generated for every layer.
(def solvable-spec
  {:name 'nnrat/farkas-elim-chain-solvable :kind :definition :universes []
   :type (function/arrow list-layer list-nnrat nnrat list-nnrat 'Prop)
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['survivor nnrat]]
      (terminal-step-prop
       'layers 'terminal-lowers 'terminal-u0 'terminal-urest 'survivor))))})

(def definition-specs
  [chain-lower-spec chain-feasible-spec open-reduced-spec open-solvable-spec
   reduced-spec solvable-spec])

;; Open-chain induction -----------------------------------------------------

(def open-extends-spec
  (let [motive
        (function/lam
         [['ys list-layer]]
         (function/forall
          [['survivor nnrat]
           ['reduced-feasible (open-reduced 'ys 'survivor)]]
          (open-solvable 'ys 'survivor)))]
    {:name 'nnrat/farkas-elim-chain-open-extends :universes []
     :type
     (function/forall
      [['layers list-layer] ['survivor nnrat]
       ['reduced-feasible (open-reduced 'layers 'survivor)]]
      (open-solvable 'layers 'survivor))
     :value
     (function/lam
      [['layers list-layer] ['survivor nnrat]
       ['reduced-feasible (open-reduced 'layers 'survivor)]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       layer motive
       (function/lam
        [['value nnrat]
         ['base-reduced (open-reduced
                         (function/app
                          (function/const* 'data/nil [type-level]) layer)
                         'value)]]
        (right-conjunct (proposition/truth) (at-most nnrat-zero 'value)
                        'base-reduced))
       (function/lam
        [['entry layer] ['tail list-layer]
         ['ih (function/app motive 'tail)]
         ['value nnrat]
         ['step-reduced
          (open-reduced
           (function/app (function/const* 'data/cons [type-level])
                         layer 'entry 'tail)
           'value)]]
        (let [augmented (augmented-lowers 'entry 'tail)
              tail-feasible-prop (chain-feasible 'tail)
              local-reduced-prop
              (list-reduced augmented
                            (layer-u0 'entry) (layer-urest 'entry))
              step-feasible-prop
              (proposition/conjunction tail-feasible-prop local-reduced-prop)
              transferred-prop
              (at-most (max-lb augmented) 'value)
              step-feasible
              (left-conjunct step-feasible-prop transferred-prop
                             'step-reduced)
              transferred
              (right-conjunct step-feasible-prop transferred-prop
                              'step-reduced)
              tail-feasible
              (left-conjunct tail-feasible-prop local-reduced-prop
                             step-feasible)
              local-reduced
              (right-conjunct tail-feasible-prop local-reduced-prop
                              step-feasible)
              coupled-prop
              (coupled-reduced augmented
                               (layer-u0 'entry) (layer-urest 'entry) 'value)
              coupled-proof
              (conjoin local-reduced-prop transferred-prop
                       local-reduced transferred)
              coupled-solution
              (function/app
               (function/const* 'nnrat/farkas-elim-coupled-extends [])
               augmented (layer-u0 'entry) (layer-urest 'entry) 'value
               coupled-proof)
              coupled-predicate
              (function/lam
               [['candidate nnrat]]
               (proposition/conjunction
                (ge-all augmented 'candidate)
                (proposition/conjunction
                 (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                 (at-most 'candidate 'value))))
              result
              (open-solvable
               (function/app (function/const* 'data/cons [type-level])
                             layer 'entry 'tail)
               'value)
              result-predicate
              (function/lam
               [['candidate nnrat]]
               (layer-step-prop 'entry 'tail 'value 'candidate))]
          (use-witness
           coupled-predicate result coupled-solution
           (function/lam
            [['candidate nnrat]
             ['coupled-evidence
              (proposition/conjunction
               (ge-all augmented 'candidate)
               (proposition/conjunction
                (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                (at-most 'candidate 'value)))]]
            (let [augmented-bounds
                  (left-conjunct
                   (ge-all augmented 'candidate)
                   (proposition/conjunction
                    (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                    (at-most 'candidate 'value))
                   'coupled-evidence)
                  upper-and-coupling
                  (right-conjunct
                   (ge-all augmented 'candidate)
                   (proposition/conjunction
                    (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                    (at-most 'candidate 'value))
                   'coupled-evidence)
                  tail-lower-prop
                  (at-most (chain-lower 'tail) 'candidate)
                  entry-bounds-prop
                  (ge-all (layer-lowers 'entry) 'candidate)
                  tail-lower
                  (left-conjunct tail-lower-prop entry-bounds-prop
                                 augmented-bounds)
                  entry-bounds
                  (right-conjunct tail-lower-prop entry-bounds-prop
                                  augmented-bounds)
                  upper-prop
                  (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                  coupling-prop (at-most 'candidate 'value)
                  upper
                  (left-conjunct upper-prop coupling-prop
                                 upper-and-coupling)
                  coupling
                  (right-conjunct upper-prop coupling-prop
                                  upper-and-coupling)
                  tail-reduced
                  (conjoin tail-feasible-prop tail-lower-prop
                           tail-feasible tail-lower)
                  tail-solution
                  (function/app 'ih 'candidate tail-reduced)
                  coupling-and-tail
                  (conjoin coupling-prop (open-solvable 'tail 'candidate)
                           coupling tail-solution)
                  upper-rest
                  (conjoin
                   upper-prop
                   (proposition/conjunction
                    coupling-prop (open-solvable 'tail 'candidate))
                   upper coupling-and-tail)
                  step-evidence
                  (conjoin
                   entry-bounds-prop
                   (proposition/conjunction
                    upper-prop
                    (proposition/conjunction
                     coupling-prop (open-solvable 'tail 'candidate)))
                   entry-bounds upper-rest)]
              (witness result-predicate 'candidate step-evidence))))))
       'layers 'survivor 'reduced-feasible))}))

(def open-projects-spec
  (let [motive
        (function/lam
         [['ys list-layer]]
         (function/forall
          [['survivor nnrat]
           ['solution (open-solvable 'ys 'survivor)]]
          (open-reduced 'ys 'survivor)))]
    {:name 'nnrat/farkas-elim-chain-open-projects :universes []
     :type
     (function/forall
      [['layers list-layer] ['survivor nnrat]
       ['solution (open-solvable 'layers 'survivor)]]
      (open-reduced 'layers 'survivor))
     :value
     (function/lam
      [['layers list-layer] ['survivor nnrat]
       ['solution (open-solvable 'layers 'survivor)]]
      (function/app
       (function/const* 'data/List.rec [type-level zero-level])
       layer motive
       (function/lam
        [['value nnrat] ['base-solution (at-most nnrat-zero 'value)]]
        (conjoin (proposition/truth) (at-most nnrat-zero 'value)
                 (function/const* 'proposition/trivial []) 'base-solution))
       (function/lam
        [['entry layer] ['tail list-layer]
         ['ih (function/app motive 'tail)]
         ['value nnrat]
         ['step-solution
          (open-solvable
           (function/app (function/const* 'data/cons [type-level])
                         layer 'entry 'tail)
           'value)]]
        (let [augmented (augmented-lowers 'entry 'tail)
              step-predicate
              (function/lam
               [['candidate nnrat]]
               (layer-step-prop 'entry 'tail 'value 'candidate))
              result
              (open-reduced
               (function/app (function/const* 'data/cons [type-level])
                             layer 'entry 'tail)
               'value)]
          (use-witness
           step-predicate result 'step-solution
           (function/lam
            [['candidate nnrat]
             ['step-evidence
              (layer-step-prop 'entry 'tail 'value 'candidate)]]
            (let [entry-bounds-prop
                  (ge-all (layer-lowers 'entry) 'candidate)
                  upper-prop
                  (le-all (layer-u0 'entry) (layer-urest 'entry) 'candidate)
                  coupling-prop (at-most 'candidate 'value)
                  tail-solution-prop (open-solvable 'tail 'candidate)
                  upper-rest-prop
                  (proposition/conjunction
                   upper-prop
                   (proposition/conjunction coupling-prop tail-solution-prop))
                  entry-bounds
                  (left-conjunct entry-bounds-prop upper-rest-prop
                                 'step-evidence)
                  upper-rest
                  (right-conjunct entry-bounds-prop upper-rest-prop
                                  'step-evidence)
                  coupling-tail-prop
                  (proposition/conjunction coupling-prop tail-solution-prop)
                  upper
                  (left-conjunct upper-prop coupling-tail-prop upper-rest)
                  coupling-tail
                  (right-conjunct upper-prop coupling-tail-prop upper-rest)
                  coupling
                  (left-conjunct coupling-prop tail-solution-prop
                                 coupling-tail)
                  tail-solution
                  (right-conjunct coupling-prop tail-solution-prop
                                  coupling-tail)
                  tail-reduced (function/app 'ih 'candidate tail-solution)
                  tail-feasible-prop (chain-feasible 'tail)
                  tail-lower-prop (at-most (chain-lower 'tail) 'candidate)
                  tail-feasible
                  (left-conjunct tail-feasible-prop tail-lower-prop
                                 tail-reduced)
                  tail-lower
                  (right-conjunct tail-feasible-prop tail-lower-prop
                                  tail-reduced)
                  augmented-bounds-prop (ge-all augmented 'candidate)
                  augmented-bounds
                  (conjoin tail-lower-prop entry-bounds-prop
                           tail-lower entry-bounds)
                  coupled-predicate
                  (function/lam
                   [['v nnrat]]
                   (proposition/conjunction
                    (ge-all augmented 'v)
                    (proposition/conjunction
                     (le-all (layer-u0 'entry) (layer-urest 'entry) 'v)
                     (at-most 'v 'value))))
                  upper-and-coupling
                  (conjoin upper-prop coupling-prop upper coupling)
                  coupled-evidence
                  (conjoin
                   augmented-bounds-prop
                   (proposition/conjunction upper-prop coupling-prop)
                   augmented-bounds upper-and-coupling)
                  coupled-solution
                  (witness coupled-predicate 'candidate coupled-evidence)
                  coupled-reduction
                  (function/app
                   (function/const* 'nnrat/farkas-elim-coupled-projects [])
                   augmented (layer-u0 'entry) (layer-urest 'entry) 'value
                   coupled-solution)
                  local-reduced-prop
                  (list-reduced augmented
                                (layer-u0 'entry) (layer-urest 'entry))
                  transferred-prop (at-most (max-lb augmented) 'value)
                  local-reduced
                  (left-conjunct local-reduced-prop transferred-prop
                                 coupled-reduction)
                  transferred
                  (right-conjunct local-reduced-prop transferred-prop
                                  coupled-reduction)
                  step-feasible-prop
                  (proposition/conjunction tail-feasible-prop
                                           local-reduced-prop)
                  step-feasible
                  (conjoin tail-feasible-prop local-reduced-prop
                           tail-feasible local-reduced)]
              (conjoin step-feasible-prop transferred-prop
                       step-feasible transferred))))))
       'layers 'survivor 'solution))}))

(def open-solvable-iff-spec
  {:name 'nnrat/farkas-elim-chain-open-solvable-iff :universes []
   :type
   (function/forall
    [['layers list-layer] ['survivor nnrat]]
    (proposition/equivalence
     (open-reduced 'layers 'survivor)
     (open-solvable 'layers 'survivor)))
   :value
   (function/lam
    [['layers list-layer] ['survivor nnrat]]
    (let [reduced-prop (open-reduced 'layers 'survivor)
          solvable-prop (open-solvable 'layers 'survivor)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['evidence reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-chain-open-extends [])
         'layers 'survivor 'evidence))
       (function/lam
        [['evidence solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-chain-open-projects [])
         'layers 'survivor 'evidence)))))} )

;; Closing the survivor -----------------------------------------------------

(def extends-spec
  {:name 'nnrat/farkas-elim-chain-extends :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['reduced-feasible
      (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]]
    (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['reduced-feasible
      (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]]
    (let [chain-feasible-prop (chain-feasible 'layers)
          final-lowers
          (cons-nnrat (chain-lower 'layers) 'terminal-lowers)
          final-reduced-prop
          (list-reduced final-lowers 'terminal-u0 'terminal-urest)
          chain-feasible-proof
          (left-conjunct chain-feasible-prop final-reduced-prop
                         'reduced-feasible)
          final-reduced-proof
          (right-conjunct chain-feasible-prop final-reduced-prop
                          'reduced-feasible)
          final-solution
          (function/app
           (function/const* 'nnrat/farkas-elim-list-extends [])
           final-lowers 'terminal-u0 'terminal-urest final-reduced-proof)
          final-predicate
          (function/lam
           [['value nnrat]]
           (proposition/conjunction
            (ge-all final-lowers 'value)
            (le-all 'terminal-u0 'terminal-urest 'value)))
          result (solvable 'layers 'terminal-lowers
                           'terminal-u0 'terminal-urest)
          result-predicate
          (function/lam
           [['value nnrat]]
           (terminal-step-prop
            'layers 'terminal-lowers
            'terminal-u0 'terminal-urest 'value))]
      (use-witness
       final-predicate result final-solution
       (function/lam
        [['value nnrat]
         ['final-evidence
          (proposition/conjunction
           (ge-all final-lowers 'value)
           (le-all 'terminal-u0 'terminal-urest 'value))]]
        (let [all-lowers
              (left-conjunct
               (ge-all final-lowers 'value)
               (le-all 'terminal-u0 'terminal-urest 'value)
               'final-evidence)
              terminal-upper
              (right-conjunct
               (ge-all final-lowers 'value)
               (le-all 'terminal-u0 'terminal-urest 'value)
               'final-evidence)
              propagated-prop (at-most (chain-lower 'layers) 'value)
              terminal-lowers-prop (ge-all 'terminal-lowers 'value)
              propagated
              (left-conjunct propagated-prop terminal-lowers-prop all-lowers)
              terminal-lower-proof
              (right-conjunct propagated-prop terminal-lowers-prop all-lowers)
              open-reduced-proof
              (conjoin chain-feasible-prop propagated-prop
                       chain-feasible-proof propagated)
              open-solution
              (function/app
               (function/const* 'nnrat/farkas-elim-chain-open-extends [])
               'layers 'value open-reduced-proof)
              upper-and-chain
              (conjoin
               (le-all 'terminal-u0 'terminal-urest 'value)
               (open-solvable 'layers 'value)
               terminal-upper open-solution)
              terminal-evidence
              (conjoin
               terminal-lowers-prop
               (proposition/conjunction
                (le-all 'terminal-u0 'terminal-urest 'value)
                (open-solvable 'layers 'value))
               terminal-lower-proof upper-and-chain)]
          (witness result-predicate 'value terminal-evidence))))))})

(def projects-spec
  {:name 'nnrat/farkas-elim-chain-projects :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['solution
      (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]]
    (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]
     ['solution
      (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]]
    (let [terminal-predicate
          (function/lam
           [['value nnrat]]
           (terminal-step-prop
            'layers 'terminal-lowers
            'terminal-u0 'terminal-urest 'value))
          result
          (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]
      (use-witness
       terminal-predicate result 'solution
       (function/lam
        [['value nnrat]
         ['terminal-evidence
          (terminal-step-prop
           'layers 'terminal-lowers
           'terminal-u0 'terminal-urest 'value)]]
        (let [terminal-lowers-prop (ge-all 'terminal-lowers 'value)
              terminal-upper-prop
              (le-all 'terminal-u0 'terminal-urest 'value)
              open-solution-prop (open-solvable 'layers 'value)
              upper-chain-prop
              (proposition/conjunction terminal-upper-prop open-solution-prop)
              terminal-lower-proof
              (left-conjunct terminal-lowers-prop upper-chain-prop
                             'terminal-evidence)
              upper-chain
              (right-conjunct terminal-lowers-prop upper-chain-prop
                              'terminal-evidence)
              terminal-upper
              (left-conjunct terminal-upper-prop open-solution-prop upper-chain)
              open-solution
              (right-conjunct terminal-upper-prop open-solution-prop upper-chain)
              open-reduction
              (function/app
               (function/const* 'nnrat/farkas-elim-chain-open-projects [])
               'layers 'value open-solution)
              chain-feasible-prop (chain-feasible 'layers)
              propagated-prop (at-most (chain-lower 'layers) 'value)
              chain-feasible-proof
              (left-conjunct chain-feasible-prop propagated-prop open-reduction)
              propagated
              (right-conjunct chain-feasible-prop propagated-prop open-reduction)
              final-lowers
              (cons-nnrat (chain-lower 'layers) 'terminal-lowers)
              all-final-lowers-prop (ge-all final-lowers 'value)
              all-final-lowers
              (conjoin propagated-prop terminal-lowers-prop
                       propagated terminal-lower-proof)
              final-predicate
              (function/lam
               [['candidate nnrat]]
               (proposition/conjunction
                (ge-all final-lowers 'candidate)
                (le-all 'terminal-u0 'terminal-urest 'candidate)))
              final-evidence
              (conjoin all-final-lowers-prop terminal-upper-prop
                       all-final-lowers terminal-upper)
              final-solution
              (witness final-predicate 'value final-evidence)
              final-reduced-prop
              (list-reduced final-lowers 'terminal-u0 'terminal-urest)
              final-reduced-proof
              (function/app
               (function/const* 'nnrat/farkas-elim-list-projects [])
               final-lowers 'terminal-u0 'terminal-urest final-solution)]
          (conjoin chain-feasible-prop final-reduced-prop
                   chain-feasible-proof final-reduced-proof))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-chain-solvable-iff :universes []
   :type
   (function/forall
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (proposition/equivalence
     (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)
     (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)))
   :value
   (function/lam
    [['layers list-layer] ['terminal-lowers list-nnrat]
     ['terminal-u0 nnrat] ['terminal-urest list-nnrat]]
    (let [reduced-prop
          (reduced 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)
          solvable-prop
          (solvable 'layers 'terminal-lowers 'terminal-u0 'terminal-urest)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['evidence reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-chain-extends [])
         'layers 'terminal-lowers 'terminal-u0 'terminal-urest 'evidence))
       (function/lam
        [['evidence solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-chain-projects [])
         'layers 'terminal-lowers 'terminal-u0 'terminal-urest 'evidence)))))} )

(def theorem-specs
  [open-extends-spec open-projects-spec open-solvable-iff-spec
   extends-spec projects-spec solvable-iff-spec])

;; The coupled extension installs the list development transitively.  Both are
;; required here explicitly because the closing theorem also uses list
;; elimination directly; proposition supplies the proof-data encodings.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-coupled])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-chain (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-chain))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
