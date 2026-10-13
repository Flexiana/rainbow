(ns rainbow.math.rational.nnrat.farkas-elim-affine-coupled
  "Brick 3 of the general LP strong-duality Fourier-Motzkin encoding
 : elimination of an nnrat variable v
  whose upper coupling carries an additive SURVIVOR-SUM term.

  Bricks 1-2 coupled v to a single survivor (a*v <= w, w <= a*v). A real
  constraint row isolating x_k reads (subtraction-free)
  A_ik*x_k + sum_{j!=k} A_ij*x_j <= b_i: the coefficient a=A_ik on the
  eliminated variable, PLUS an additive block s = sum_{j!=k} A_ij*x_j over
  the surviving variables, all bounded by the constant b=b_i. This brick
  eliminates v from the affine coupling `a*v + s <= b`, transferring
  `a*max-lb(lowers) + s <= b` onto the survivors. Here s is an arbitrary
  nnrat -- the elimination does not depend on its being a sum; brick 4
  instantiates s to the map-sum block and tracks how it is rebuilt.

  Structural mirror of brick 1 with the additive term carried through: in
  the projection, max-lb <= value gives a*max-lb <= a*value
  (multiply-monotone), then a*max-lb + s <= a*value + s (add-right-monotone),
  then a*value + s <= b (the coupling) closes it by transitivity. No
  positivity required. Native proof data, axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as coupled]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- reduced [lowers u0 urest a s b]
  (function/app (function/const* 'nnrat/farkas-elim-affine-coupled-reduced [])
                lowers u0 urest a s b))
(defn- solvable [lowers u0 urest a s b]
  (function/app (function/const* 'nnrat/farkas-elim-affine-coupled-solvable [])
                lowers u0 urest a s b))

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
(defn- add-right-monotone [addend left right ordered]
  (function/app (function/const* 'nnrat/add-right-monotone [])
                addend left right ordered))

(defn- coupling [a value s b]
  (at-most (add (multiply a value) s) b))

(defn- satisfies [lowers u0 urest a s b value]
  (proposition/conjunction
   (ge-all lowers value)
   (proposition/conjunction
    (le-all u0 urest value)
    (coupling a value s b))))

(def reduced-spec
  {:name 'nnrat/farkas-elim-affine-coupled-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]]
    (proposition/conjunction
     (le-all 'u0 'urest (max-lb 'lowers))
     (coupling 'a (max-lb 'lowers) 's 'b)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-affine-coupled-solvable
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (satisfies 'lowers 'u0 'urest 'a 's 'b 'value))))})

(def definition-specs [reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-affine-coupled-extends
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'a 's 'b)]]
    (solvable 'lowers 'u0 'urest 'a 's 'b))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]
     ['reduced-feasible (reduced 'lowers 'u0 'urest 'a 's 'b)]]
    (let [value (max-lb 'lowers)
          upper-prop (le-all 'u0 'urest value)
          coupling-prop (coupling 'a value 's 'b)
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
           (satisfies 'lowers 'u0 'urest 'a 's 'b 'candidate))]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-affine-coupled-projects
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'a 's 'b)]]
    (reduced 'lowers 'u0 'urest 'a 's 'b))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]
     ['solution (solvable 'lowers 'u0 'urest 'a 's 'b)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (satisfies 'lowers 'u0 'urest 'a 's 'b 'candidate))
          result (reduced 'lowers 'u0 'urest 'a 's 'b)]
      (use-witness
       predicate result 'solution
       (function/lam
        [['value nnrat]
         ['satisfies-proof
          (satisfies 'lowers 'u0 'urest 'a 's 'b 'value)]]
        (let [lower-prop (ge-all 'lowers 'value)
              upper-prop (le-all 'u0 'urest 'value)
              coupling-prop (coupling 'a 'value 's 'b)
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
              ;; a*max-lb <= a*value, then + s on both sides, then <= b.
              scaled-mono
              (multiply-monotone 'a (max-lb 'lowers) 'value
                                 folded-at-most-value)
              summed-mono
              (add-right-monotone 's (multiply 'a (max-lb 'lowers))
                                  (multiply 'a 'value) scaled-mono)
              transferred-proof
              (at-most-transitive
               (add (multiply 'a (max-lb 'lowers)) 's)
               (add (multiply 'a 'value) 's) 'b
               summed-mono coupling-proof)]
          (conjoin
           (le-all 'u0 'urest (max-lb 'lowers))
           (coupling 'a (max-lb 'lowers) 's 'b)
           reduced-upper-proof transferred-proof))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-affine-coupled-solvable-iff
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]]
    (proposition/equivalence
     (reduced 'lowers 'u0 'urest 'a 's 'b)
     (solvable 'lowers 'u0 'urest 'a 's 'b)))
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['s nnrat] ['b nnrat]]
    (let [reduced-prop (reduced 'lowers 'u0 'urest 'a 's 'b)
          solvable-prop (solvable 'lowers 'u0 'urest 'a 's 'b)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-coupled-extends [])
         'lowers 'u0 'urest 'a 's 'b 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-coupled-projects [])
         'lowers 'u0 'urest 'a 's 'b 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      coupled/extend-environment
      multiply-monotone/extend-environment
      add-monotone/extend-environment
      (support/extend-with :nnrat-farkas-elim-affine-coupled
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
