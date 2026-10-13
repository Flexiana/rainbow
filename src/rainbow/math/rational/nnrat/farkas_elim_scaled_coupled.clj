(ns rainbow.math.rational.nnrat.farkas-elim-scaled-coupled
  "Brick 1 of the general LP strong-duality Fourier-Motzkin encoding
 : elimination of an nnrat variable v
  that appears with a COEFFICIENT in its coupling to a survivor.

  Besides constant lower and non-empty upper families for v, the system
  contains a*v <= w (the surviving variable w carries coefficient a on the
  eliminated v -- the shape a real constraint row A_ik*x_k <= ... produces,
  which the coefficient-1 coupled primitive
  nnrat/farkas-elim-coupled-solvable-iff cannot express). Eliminating v
  preserves the list-sized reduced condition and transfers
  a*max-lb(lowers) <= w onto the surviving variable.

  The proof mirrors nnrat_farkas_elim_coupled.clj exactly; the only new
  content is the projection's transferred bound: max-lb <= value gives
  a*max-lb <= a*value by nnrat/multiply-monotone, and a*value <= w closes
  it by transitivity. No positivity of a is needed for either direction
  (multiply-monotone holds for every factor). Native proof data,
  axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as coupled]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- reduced [lowers u0 urest a w]
  (function/app (function/const* 'nnrat/farkas-elim-scaled-coupled-reduced [])
                lowers u0 urest a w))
(defn- solvable [lowers u0 urest a w]
  (function/app (function/const* 'nnrat/farkas-elim-scaled-coupled-solvable [])
                lowers u0 urest a w))

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
(defn- multiply-monotone [factor left right ordered]
  (function/app (function/const* 'nnrat/multiply-monotone [])
                factor left right ordered))

(defn- satisfies [lowers u0 urest a w value]
  (proposition/conjunction
   (ge-all lowers value)
   (proposition/conjunction
    (le-all u0 urest value)
    (at-most (multiply a value) w))))

(def reduced-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]]
    (proposition/conjunction
     (le-all 'u0 'urest (max-lb 'lowers))
     (at-most (multiply 'a (max-lb 'lowers)) 'w)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-solvable
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (satisfies 'lowers 'u0 'urest 'a 'w 'value))))})

(def definition-specs [reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-extends
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'a 'w)]]
    (solvable 'lowers 'u0 'urest 'a 'w))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'a 'w)]]
    (let [value (max-lb 'lowers)
          upper-prop (le-all 'u0 'urest value)
          coupling-prop (at-most (multiply 'a value) 'w)
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
           (satisfies 'lowers 'u0 'urest 'a 'w 'candidate))]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-projects
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'a 'w)]]
    (reduced 'lowers 'u0 'urest 'a 'w))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'a 'w)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (satisfies 'lowers 'u0 'urest 'a 'w 'candidate))
          result (reduced 'lowers 'u0 'urest 'a 'w)]
      (use-witness
       predicate result 'solution
       (function/lam
        [['value nnrat]
         ['satisfies-proof
          (satisfies 'lowers 'u0 'urest 'a 'w 'value)]]
        (let [lower-prop (ge-all 'lowers 'value)
              upper-prop (le-all 'u0 'urest 'value)
              coupling-prop (at-most (multiply 'a 'value) 'w)
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
              ;; a*max-lb <= a*value (multiply-monotone) then a*value <= w.
              scaled-mono
              (multiply-monotone 'a (max-lb 'lowers) 'value
                                 folded-at-most-value)
              transferred-proof
              (at-most-transitive (multiply 'a (max-lb 'lowers))
                                  (multiply 'a 'value) 'w
                                  scaled-mono coupling-proof)]
          (conjoin
           (le-all 'u0 'urest (max-lb 'lowers))
           (at-most (multiply 'a (max-lb 'lowers)) 'w)
           reduced-upper-proof transferred-proof))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-solvable-iff
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]]
    (proposition/equivalence
     (reduced 'lowers 'u0 'urest 'a 'w)
     (solvable 'lowers 'u0 'urest 'a 'w)))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]]
    (let [reduced-prop (reduced 'lowers 'u0 'urest 'a 'w)
          solvable-prop (solvable 'lowers 'u0 'urest 'a 'w)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-scaled-coupled-extends [])
         'lowers 'u0 'urest 'a 'w 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-scaled-coupled-projects [])
         'lowers 'u0 'urest 'a 'w 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-coupled rainbow.math.rational.nnrat.multiply-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-scaled-coupled (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-scaled-coupled))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
