(ns rainbow.math.rational.nnrat.farkas-elim-coupled
  "Constructive elimination of an nnrat variable coupled to a survivor.

  Besides constant lower and non-empty upper families for v, the original
  system contains v <= w.  Eliminating v preserves the ordinary list-sized
  reduced condition and transfers max-lb(lowers) <= w onto the surviving
  variable.  The witness and projection are native proof data and axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- reduced [lowers u0 urest w]
  (function/app (function/const* 'nnrat/farkas-elim-coupled-reduced [])
                lowers u0 urest w))
(defn- solvable [lowers u0 urest w]
  (function/app (function/const* 'nnrat/farkas-elim-coupled-solvable [])
                lowers u0 urest w))

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
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))

(defn- satisfies [lowers u0 urest w value]
  (proposition/conjunction
   (ge-all lowers value)
   (proposition/conjunction
    (le-all u0 urest value)
    (at-most value w))))

(def reduced-spec
  {:name 'nnrat/farkas-elim-coupled-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]]
    (proposition/conjunction
     (le-all 'u0 'urest (max-lb 'lowers))
     (at-most (max-lb 'lowers) 'w)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-coupled-solvable
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (satisfies 'lowers 'u0 'urest 'w 'value))))})

(def definition-specs [reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-coupled-extends
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'w)]]
    (solvable 'lowers 'u0 'urest 'w))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'w)]]
    (let [value (max-lb 'lowers)
          upper-prop (le-all 'u0 'urest value)
          coupling-prop (at-most value 'w)
          upper-proof
          (left-conjunct upper-prop coupling-prop 'reduced-feasible)
          coupling-proof
          (right-conjunct upper-prop coupling-prop 'reduced-feasible)
          tail-proof
          (conjoin upper-prop coupling-prop upper-proof coupling-proof)
          satisfies-proof
          (conjoin
           (ge-all 'lowers value)
           (proposition/conjunction upper-prop coupling-prop)
           (function/app (function/const* 'nnrat/max-lb-is-upper [])
                         'lowers)
           tail-proof)
          predicate
          (function/lam
           [['candidate nnrat]]
           (satisfies 'lowers 'u0 'urest 'w 'candidate))]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-coupled-projects
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'w)]]
    (reduced 'lowers 'u0 'urest 'w))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'w)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (satisfies 'lowers 'u0 'urest 'w 'candidate))
          result (reduced 'lowers 'u0 'urest 'w)]
      (use-witness
       predicate result 'solution
       (function/lam
        [['value nnrat]
         ['satisfies-proof
          (satisfies 'lowers 'u0 'urest 'w 'value)]]
        (let [lower-prop (ge-all 'lowers 'value)
              upper-prop (le-all 'u0 'urest 'value)
              coupling-prop (at-most 'value 'w)
              tail-prop (proposition/conjunction upper-prop coupling-prop)
              lower-proof
              (left-conjunct lower-prop tail-prop 'satisfies-proof)
              tail-proof
              (right-conjunct lower-prop tail-prop 'satisfies-proof)
              upper-proof
              (left-conjunct upper-prop coupling-prop tail-proof)
              coupling-proof
              (right-conjunct upper-prop coupling-prop tail-proof)
              folded-at-most-value
              (function/app (function/const* 'nnrat/max-lb-least [])
                            'lowers 'value lower-proof)
              reduced-upper-proof
              (function/app (function/const* 'nnrat/le-all-antitone [])
                            'u0 'urest (max-lb 'lowers) 'value
                            folded-at-most-value upper-proof)
              transferred-proof
              (at-most-transitive (max-lb 'lowers) 'value 'w
                                  folded-at-most-value coupling-proof)]
          (conjoin
           (le-all 'u0 'urest (max-lb 'lowers))
           (at-most (max-lb 'lowers) 'w)
           reduced-upper-proof transferred-proof))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-coupled-solvable-iff
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]]
    (proposition/equivalence
     (reduced 'lowers 'u0 'urest 'w)
     (solvable 'lowers 'u0 'urest 'w)))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat] ['w nnrat]]
    (let [reduced-prop (reduced 'lowers 'u0 'urest 'w)
          solvable-prop (solvable 'lowers 'u0 'urest 'w)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-coupled-extends [])
         'lowers 'u0 'urest 'w 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-coupled-projects [])
         'lowers 'u0 'urest 'w 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      elim-list/extend-environment
      (support/extend-with :nnrat-farkas-elim-coupled
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
