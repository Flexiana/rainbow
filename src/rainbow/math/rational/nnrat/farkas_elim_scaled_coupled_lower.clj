(ns rainbow.math.rational.nnrat.farkas-elim-scaled-coupled-lower
  "Brick 2 of the general LP strong-duality Fourier-Motzkin encoding
 : elimination of an nnrat variable v
  whose coupling to a survivor is a scaled LOWER bound.

  Where brick 1 (nnrat_farkas_elim_scaled_coupled.clj) handled an upper
  coupling a*v <= w, this handles the lower coupling w <= a*v -- the shape
  a `>=` row (objective-boundary c.x >= t) produces once c.x is isolated.
  v is bounded below by a constant lower family and above by a non-empty
  upper family; eliminating v (witness the LARGEST feasible value,
  min-ub of the uppers) preserves the reduced condition and transfers
  w <= a*min-ub(uppers) onto the survivor.

  Symmetric to brick 1 with min-ub in place of max-lb. The projection needs
  ge-all lowers value with value <= min-ub to give ge-all lowers min-ub;
  that monotonicity of ge-all is the dual of the list module's
  le-all-antitone and was missing, so nnrat/ge-all-monotone is proved here
  as the brick's supporting lemma (a plain List.rec induction over the
  lowers). Native proof data, axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-list :as elim-list]
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
(defn- min-ub [u0 urest]
  (function/app (function/const* 'nnrat/min-ub []) u0 urest))
(defn- nil-nnrat []
  (function/app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(defn- reduced [lowers u0 urest a w]
  (function/app
   (function/const* 'nnrat/farkas-elim-scaled-coupled-lower-reduced [])
   lowers u0 urest a w))
(defn- solvable [lowers u0 urest a w]
  (function/app
   (function/const* 'nnrat/farkas-elim-scaled-coupled-lower-solvable [])
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
(defn- ge-all-monotone [lowers value target ordered base-proof]
  (function/app (function/const* 'nnrat/ge-all-monotone [])
                lowers value target ordered base-proof))

;; Supporting lemma: ge-all is monotone in its value. Dual of the list
;; module's le-all-antitone; proved here because this brick is its owner.
(def ge-all-monotone-spec
  {:name 'nnrat/ge-all-monotone :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['value nnrat] ['target nnrat]
     ['ordered (at-most 'value 'target)]
     ['base-proof (ge-all 'lowers 'value)]]
    (ge-all 'lowers 'target))
   :value
   (function/lam
    [['lowers list-nnrat] ['value nnrat] ['target nnrat]
     ['ordered (at-most 'value 'target)]
     ['base-proof (ge-all 'lowers 'value)]]
    (let [motive (function/lam
                  [['ls list-nnrat]]
                  (function/arrow (ge-all 'ls 'value) (ge-all 'ls 'target)))
          nil-case (function/lam
                    [['hnil (ge-all (nil-nnrat) 'value)]]
                    (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['lower nnrat] ['tail list-nnrat]
            ['ih (function/arrow (ge-all 'tail 'value)
                                 (ge-all 'tail 'target))]]
           (function/lam
            [['hcons (ge-all (cons-nnrat 'lower 'tail) 'value)]]
            (let [lo-le-val (left-conjunct (at-most 'lower 'value)
                                           (ge-all 'tail 'value) 'hcons)
                  tail-ge (right-conjunct (at-most 'lower 'value)
                                          (ge-all 'tail 'value) 'hcons)]
              (conjoin (at-most 'lower 'target) (ge-all 'tail 'target)
                       (at-most-transitive 'lower 'value 'target
                                           lo-le-val 'ordered)
                       (function/app 'ih tail-ge)))))]
      (function/app
       (function/app (function/const* 'data/List.rec [type-level zero-level])
                     nnrat motive nil-case cons-case 'lowers)
       'base-proof)))})

(defn- satisfies [lowers u0 urest a w value]
  (proposition/conjunction
   (ge-all lowers value)
   (proposition/conjunction
    (le-all u0 urest value)
    (at-most w (multiply a value)))))

(def reduced-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-lower-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat nnrat list-nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['u0 nnrat] ['urest list-nnrat]
     ['a nnrat] ['w nnrat]]
    (proposition/conjunction
     (ge-all 'lowers (min-ub 'u0 'urest))
     (at-most 'w (multiply 'a (min-ub 'u0 'urest)))))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-lower-solvable
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

(def definition-specs [ge-all-monotone-spec reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-lower-extends
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
    (let [value (min-ub 'u0 'urest)
          lower-prop (ge-all 'lowers value)
          coupling-prop (at-most 'w (multiply 'a value))
          lower-proof
          (left-conjunct lower-prop coupling-prop 'reduced-feasible)
          coupling-proof
          (right-conjunct lower-prop coupling-prop 'reduced-feasible)
          upper-proof
          (function/app (function/const* 'nnrat/min-ub-is-lower [])
                        'u0 'urest)
          tail-proof
          (conjoin (le-all 'u0 'urest value) coupling-prop
                   upper-proof coupling-proof)
          satisfies-proof
          (conjoin
           lower-prop
           (proposition/conjunction (le-all 'u0 'urest value) coupling-prop)
           lower-proof tail-proof)
          predicate
          (function/lam
           [['candidate nnrat]]
           (satisfies 'lowers 'u0 'urest 'a 'w 'candidate))]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-lower-projects
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
              coupling-prop (at-most 'w (multiply 'a 'value))
              tail-prop (proposition/conjunction upper-prop coupling-prop)
              lower-proof
              (left-conjunct lower-prop tail-prop 'satisfies-proof)
              tail-proof
              (right-conjunct lower-prop tail-prop 'satisfies-proof)
              upper-proof
              (left-conjunct upper-prop coupling-prop tail-proof)
              coupling-proof
              (right-conjunct upper-prop coupling-prop tail-proof)
              ;; value <= min-ub, so ge-all lowers value lifts to min-ub.
              value-le-min
              (function/app (function/const* 'nnrat/min-ub-greatest [])
                            'u0 'urest 'value upper-proof)
              reduced-lower-proof
              (ge-all-monotone 'lowers 'value (min-ub 'u0 'urest)
                               value-le-min lower-proof)
              ;; w <= a*value <= a*min-ub.
              scaled-mono
              (multiply-monotone 'a 'value (min-ub 'u0 'urest) value-le-min)
              transferred-proof
              (at-most-transitive 'w (multiply 'a 'value)
                                  (multiply 'a (min-ub 'u0 'urest))
                                  coupling-proof scaled-mono)]
          (conjoin
           (ge-all 'lowers (min-ub 'u0 'urest))
           (at-most 'w (multiply 'a (min-ub 'u0 'urest)))
           reduced-lower-proof transferred-proof))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-scaled-coupled-lower-solvable-iff
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
         (function/const* 'nnrat/farkas-elim-scaled-coupled-lower-extends [])
         'lowers 'u0 'urest 'a 'w 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-scaled-coupled-lower-projects [])
         'lowers 'u0 'urest 'a 'w 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.nnrat.multiply-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-scaled-coupled-lower (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-scaled-coupled-lower))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
