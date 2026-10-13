(ns rainbow.math.rational.nnrat.farkas-elim-affine-list
  "Brick 4 of the general LP strong-duality Fourier-Motzkin encoding
 : the one-primal-variable FM
  elimination step over a LIST of affine upper rows -- the first genuinely
  new formalization of the lane.

  A real elimination sees v constrained by many rows at once. Each row is a
  triple (a, s, b) meaning a*v + s <= b, with a the coefficient on the
  eliminated v, s the additive survivor-sum block, b the constant bound
  (brick 3's affine coupling, per row). Rows are `data/Product`-triples in
  a List; `rows-satisfied rows value` folds the per-row coupling with
  conjunction. v is bounded below by a constant lower family. Eliminating v
  (witness max-lb(lowers), the smallest feasible value) is solvable iff
  every row holds at max-lb -- rows-satisfied rows (max-lb lowers).

  The projection is the new content: it maps brick 3's per-row argument
  (max-lb <= value gives a*max-lb <= a*value by multiply-monotone, then
  + s by add-right-monotone, then <= b by transitivity) across the whole
  row list by List.rec induction. The extension witnesses max-lb directly.
  Native proof data, axiom-free."
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
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
;; A row (a, (s, b)): coefficient, survivor-sum block, bound.
(def row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-row
  (function/app (function/const* 'data/List [type-level]) row))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- ge-all [lowers value]
  (function/app (function/const* 'nnrat/ge-all []) lowers value))
(defn- max-lb [lowers]
  (function/app (function/const* 'nnrat/max-lb []) lowers))
(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- row-a [r] (first-of nnrat pair-nnrat r))
(defn- row-sb [r] (second-of nnrat pair-nnrat r))
(defn- row-s [r] (first-of nnrat nnrat (row-sb r)))
(defn- row-b [r] (second-of nnrat nnrat (row-sb r)))
(defn- coupling-at [r value]
  (at-most (add (multiply (row-a r) value) (row-s r)) (row-b r)))

(defn- rows-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows value))
(defn- reduced [lowers rows]
  (function/app (function/const* 'nnrat/farkas-elim-affine-list-reduced [])
                lowers rows))
(defn- solvable [lowers rows]
  (function/app (function/const* 'nnrat/farkas-elim-affine-list-solvable [])
                lowers rows))

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

;; rows-satisfied rows value: every row's affine coupling holds at value.
(def rows-satisfied-spec
  {:name 'nnrat/farkas-elim-affine-rows-satisfied
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
  {:name 'nnrat/farkas-elim-affine-list-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat list-row 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]]
    (rows-satisfied 'rows (max-lb 'lowers)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-affine-list-solvable
   :kind :definition
   :universes []
   :type (function/arrow list-nnrat list-row 'Prop)
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]]
    (proposition/existence
     type-level nnrat
     (function/lam
      [['value nnrat]]
      (proposition/conjunction
       (ge-all 'lowers 'value)
       (rows-satisfied 'rows 'value)))))})

(def definition-specs [rows-satisfied-spec reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-affine-list-extends
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['rows list-row]
     ['reduced-feasible (reduced 'lowers 'rows)]]
    (solvable 'lowers 'rows))
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]
     ['reduced-feasible (reduced 'lowers 'rows)]]
    (let [value (max-lb 'lowers)
          predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (ge-all 'lowers 'candidate)
            (rows-satisfied 'rows 'candidate)))
          satisfies-proof
          (conjoin
           (ge-all 'lowers value)
           (rows-satisfied 'rows value)
           (function/app (function/const* 'nnrat/max-lb-is-upper [])
                         'lowers)
           'reduced-feasible)]
      (witness predicate value satisfies-proof)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-affine-list-projects
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['rows list-row]
     ['solution (solvable 'lowers 'rows)]]
    (reduced 'lowers 'rows))
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]
     ['solution (solvable 'lowers 'rows)]]
    (let [predicate
          (function/lam
           [['candidate nnrat]]
           (proposition/conjunction
            (ge-all 'lowers 'candidate)
            (rows-satisfied 'rows 'candidate)))
          result (reduced 'lowers 'rows)]
      (use-witness
       predicate result 'solution
       (function/lam
        [['value nnrat]
         ['satisfies-proof
          (proposition/conjunction
           (ge-all 'lowers 'value)
           (rows-satisfied 'rows 'value))]]
        (let [ge-proof
              (left-conjunct (ge-all 'lowers 'value)
                             (rows-satisfied 'rows 'value) 'satisfies-proof)
              rows-v
              (right-conjunct (ge-all 'lowers 'value)
                              (rows-satisfied 'rows 'value) 'satisfies-proof)
              max-lb-le-v
              (function/app (function/const* 'nnrat/max-lb-least [])
                            'lowers 'value ge-proof)
              target (max-lb 'lowers)
              ;; map the per-row argument across the list by induction.
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
                      a (row-a 'head) s (row-s 'head) b (row-b 'head)
                      scaled
                      (multiply-monotone a target 'value max-lb-le-v)
                      summed
                      (add-right-monotone s (multiply a target)
                                          (multiply a 'value) scaled)
                      row-target-proof
                      (at-most-transitive
                       (add (multiply a target) s)
                       (add (multiply a 'value) s) b
                       summed row-v-proof)]
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
  {:name 'nnrat/farkas-elim-affine-list-solvable-iff
   :universes []
   :type
   (function/forall
    [['lowers list-nnrat] ['rows list-row]]
    (proposition/equivalence
     (reduced 'lowers 'rows)
     (solvable 'lowers 'rows)))
   :value
   (function/lam
    [['lowers list-nnrat] ['rows list-row]]
    (let [reduced-prop (reduced 'lowers 'rows)
          solvable-prop (solvable 'lowers 'rows)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-list-extends [])
         'lowers 'rows 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const* 'nnrat/farkas-elim-affine-list-projects [])
         'lowers 'rows 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      coupled/extend-environment
      multiply-monotone/extend-environment
      add-monotone/extend-environment
      (support/extend-with :nnrat-farkas-elim-affine-list
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
