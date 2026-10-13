(ns rainbow.math.rational.nnrat.farkas-elim-affine-list-lower
  "Brick 5b of the general LP strong-duality Fourier-Motzkin encoding
 : the one-variable elimination step
  over a list of affine LOWER rows -- the mirror of brick 4
  (nnrat_farkas_elim_affine_list.clj) for the other bound direction.

  Where brick 4 eliminated v from affine UPPER rows a*v+s<=b with a
  constant lower family, this eliminates v from affine LOWER rows
  w <= a*v + s with a constant UPPER family. Each row is a data/Product
  triple (a, s, w). v's largest feasible value is min-ub of the uppers, so
  eliminating v (witness min-ub) is solvable iff every lower row holds at
  min-ub: w <= a*min-ub + s. Both affine-row directions -- upper (brick 4)
  and lower (here) -- are the two input row sets the affine CROSS-PRODUCT
  (the real remaining crux; see the scoping note in the design doc)
  combines.

  Structural mirror of brick 4 with min-ub for max-lb and le-all for
  ge-all: the projection maps the per-row argument (v <= min-ub gives
  a*v <= a*min-ub by multiply-monotone, then + s by add-right-monotone,
  then w <= that by transitivity) across the list by List.rec, rows
  destructured by product/first,second. Native proof data, axiom-free."
  (:refer-clojure :exclude [reduced])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-elim-coupled :as coupled]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
;; A lower row (a, (s, w)): coefficient, additive block, lower bound w.
(def row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-row
  (function/app (function/const* 'data/List [type-level]) row))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- le-all [u0 urest value]
  (function/app (function/const* 'nnrat/le-all []) u0 urest value))
(defn- min-ub [u0 urest]
  (function/app (function/const* 'nnrat/min-ub []) u0 urest))
(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- row-a [r] (first-of nnrat pair-nnrat r))
(defn- row-sw [r] (second-of nnrat pair-nnrat r))
(defn- row-s [r] (first-of nnrat nnrat (row-sw r)))
(defn- row-w [r] (second-of nnrat nnrat (row-sw r)))
(defn- coupling-at [r value]
  (at-most (row-w r) (add (multiply (row-a r) value) (row-s r))))

(defn- rows-satisfied [rows value]
  (function/app
   (function/const* 'nnrat/farkas-elim-affine-lower-rows-satisfied [])
   rows value))
(defn- reduced [u0 urest rows]
  (function/app
   (function/const* 'nnrat/farkas-elim-affine-list-lower-reduced [])
   u0 urest rows))
(defn- solvable [u0 urest rows]
  (function/app
   (function/const* 'nnrat/farkas-elim-affine-list-lower-solvable [])
   u0 urest rows))

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

(def rows-satisfied-spec
  {:name 'nnrat/farkas-elim-affine-lower-rows-satisfied
   :kind :definition
   :universes []
   :type (function/arrow list-row nnrat 'Prop)
   :value
   (function/lam
    [['rows list-row] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     row
     (function/lam [['ignored list-row]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head row] ['tail list-row] ['ih 'Prop]]
      (proposition/conjunction (coupling-at 'head 'value) 'ih))
     'rows))})

(def reduced-spec
  {:name 'nnrat/farkas-elim-affine-list-lower-reduced
   :kind :definition
   :universes []
   :type (function/arrow nnrat list-nnrat list-row 'Prop)
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]]
    (rows-satisfied 'rows (min-ub 'u0 'urest)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-affine-list-lower-solvable
   :kind :definition
   :universes []
   :type (function/arrow nnrat list-nnrat list-row 'Prop)
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (proposition/conjunction
       (le-all 'u0 'urest 'value)
       (rows-satisfied 'rows 'value)))))})

(def definition-specs [rows-satisfied-spec reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-affine-list-lower-extends
   :universes []
   :type
   (function/forall
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]
     ['reduced-feasible (reduced 'u0 'urest 'rows)]]
    (solvable 'u0 'urest 'rows))
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]
     ['reduced-feasible (reduced 'u0 'urest 'rows)]]
    (let [value (min-ub 'u0 'urest)
          predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (le-all 'u0 'urest 'candidate)
            (rows-satisfied 'rows 'candidate)))
          satisfies-proof
          (conjoin
           (le-all 'u0 'urest value)
           (rows-satisfied 'rows value)
           (function/app (function/const* 'nnrat/min-ub-is-lower [])
                         'u0 'urest)
           'reduced-feasible)]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-affine-list-lower-projects
   :universes []
   :type
   (function/forall
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]
     ['solution (solvable 'u0 'urest 'rows)]]
    (reduced 'u0 'urest 'rows))
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]
     ['solution (solvable 'u0 'urest 'rows)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (le-all 'u0 'urest 'candidate)
            (rows-satisfied 'rows 'candidate)))
          result (reduced 'u0 'urest 'rows)]
      (use-witness
       predicate result 'solution
       (function/lam
        [['value nnrat]
         ['satisfies-proof
          (proposition/conjunction
           (le-all 'u0 'urest 'value)
           (rows-satisfied 'rows 'value))]]
        (let [le-proof
              (left-conjunct (le-all 'u0 'urest 'value)
                             (rows-satisfied 'rows 'value) 'satisfies-proof)
              rows-v
              (right-conjunct (le-all 'u0 'urest 'value)
                              (rows-satisfied 'rows 'value) 'satisfies-proof)
              value-le-min
              (function/app (function/const* 'nnrat/min-ub-greatest [])
                            'u0 'urest 'value le-proof)
              target (min-ub 'u0 'urest)
              motive
              (function/lam
               [['rs list-row]]
               (function/arrow (rows-satisfied 'rs 'value)
                               (rows-satisfied 'rs target)))
              nil-case
              (function/lam
               [['hnil (rows-satisfied
                        (function/app (function/const* 'data/nil [type-level])
                                      row)
                        'value)]]
               (function/const* 'proposition/trivial []))
              cons-case
              (function/lam
               [['head row] ['tail list-row]
                ['ih (function/arrow (rows-satisfied 'tail 'value)
                                     (rows-satisfied 'tail target))]]
               (function/lam
                [['hcons (rows-satisfied
                          (function/app (function/const* 'data/cons [type-level])
                                        row 'head 'tail)
                          'value)]]
                (let [head-coupling-v (coupling-at 'head 'value)
                      tail-prop (rows-satisfied 'tail 'value)
                      row-v-proof
                      (left-conjunct head-coupling-v tail-prop 'hcons)
                      tail-v-proof
                      (right-conjunct head-coupling-v tail-prop 'hcons)
                      a (row-a 'head) s (row-s 'head) w (row-w 'head)
                      scaled
                      (multiply-monotone a 'value target value-le-min)
                      summed
                      (add-right-monotone s (multiply a 'value)
                                          (multiply a target) scaled)
                      row-target-proof
                      (at-most-transitive
                       w (add (multiply a 'value) s)
                       (add (multiply a target) s)
                       row-v-proof summed)]
                  (conjoin
                   (coupling-at 'head target)
                   (rows-satisfied 'tail target)
                   row-target-proof
                   (function/app 'ih tail-v-proof)))))]
          (function/app
           (function/app
            (function/const* 'data/List.rec [type-level zero-level])
            row motive nil-case cons-case 'rows)
           rows-v))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-affine-list-lower-solvable-iff
   :universes []
   :type
   (function/forall
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]]
    (proposition/equivalence
     (reduced 'u0 'urest 'rows)
     (solvable 'u0 'urest 'rows)))
   :value
   (function/lam
    [['u0 nnrat] ['urest list-nnrat] ['rows list-row]]
    (let [reduced-prop (reduced 'u0 'urest 'rows)
          solvable-prop (solvable 'u0 'urest 'rows)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-list-lower-extends [])
         'u0 'urest 'rows 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-list-lower-projects [])
         'u0 'urest 'rows 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-elim-coupled rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.add-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim-affine-list-lower (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim-affine-list-lower))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
