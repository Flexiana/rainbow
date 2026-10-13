(ns rainbow.math.rational.nnrat.farkas-cross-bilist
  "Brick 6 (cross-product core) of the general LP strong-duality
  Fourier-Motzkin encoding: the
  cross-product over BOTH row lists -- a list of affine lower rows against a
  list of affine upper rows.

  The two-variable instance (5d-iii) eliminated a variable with ONE lower
  row (the objective) against a list of upper rows (5d-i). The general
  n-variable induction eliminates a variable that carries a LIST of lower
  rows AND a list of upper rows, and its reduced system is EVERY pairwise
  cross condition. This generalizes 5d-i by an outer List.rec over the lower
  rows: any v satisfying every lower row and every upper row yields, for
  each lower row, that lower's whole cross-condition list (5d-i applied per
  lower). Parameterized, no concrete arithmetic -- the reusable elimination
  step the n-variable induction folds over the variable count.

  nnrat/farkas-cross-bilist-necessary proves it; the reduced conditions are
  collected by nnrat/farkas-cross-bilist-conditions (a fold over the lower
  rows of 5d-i's per-lower fold). Reuses 5d-i
  (nnrat/farkas-cross-list-necessary) per lower row and brick 4's
  rows-satisfied for the uppers. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-cross-list :as cross-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
;; an upper row (a, (s, b)) -- brick 4's row type
(def upper-row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-upper
  (function/app (function/const* 'data/List [type-level]) upper-row))
;; a lower row (a, (s, w)) meaning w <= a*v + s
(def lower-row
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat pair-nnrat))
(def list-lower
  (function/app (function/const* 'data/List [type-level]) lower-row))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- first-of [left right value]
  (function/app (function/const* 'product/first [type-level type-level])
                left right value))
(defn- second-of [left right value]
  (function/app (function/const* 'product/second [type-level type-level])
                left right value))
(defn- lo-a [r] (first-of nnrat pair-nnrat r))
(defn- lo-sw [r] (second-of nnrat pair-nnrat r))
(defn- lo-s [r] (first-of nnrat nnrat (lo-sw r)))
(defn- lo-w [r] (second-of nnrat nnrat (lo-sw r)))
;; the lower row w <= a*v + s at value v
(defn- lower-at [r value]
  (at-most (lo-w r) (add (multiply (lo-a r) value) (lo-s r))))

;; brick 4's fold over the upper rows
(defn- uppers-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows value))
;; 5d-i's per-lower cross conditions
(defn- crosses [upper-rows a-lo s-lo w-lo]
  (function/app (function/const* 'nnrat/farkas-cross-list-conditions [])
                upper-rows a-lo s-lo w-lo))
(defn- cross-list-necessary [a-lo s-lo w-lo upper-rows value lower uppers]
  (function/app (function/const* 'nnrat/farkas-cross-list-necessary [])
                a-lo s-lo w-lo upper-rows value lower uppers))
;; this brick's fold over the lower rows
(defn- lowers-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-lowers-satisfied []) rows value))
(defn- bilist-conditions [lower-rows upper-rows]
  (function/app (function/const* 'nnrat/farkas-cross-bilist-conditions [])
                lower-rows upper-rows))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))

;; every lower row holds at value
(def lowers-satisfied-spec
  {:name 'nnrat/farkas-lowers-satisfied
   :kind :definition
   :universes []
   :type (function/arrow list-lower nnrat 'Prop)
   :value
   (function/lam
    [['rows list-lower] ['value nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     lower-row
     (function/lam [['ignored list-lower]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head lower-row] ['tail list-lower] ['ih 'Prop]]
      (proposition/conjunction (lower-at 'head 'value) 'ih))
     'rows))})

;; for each lower row, its whole 5d-i cross-condition list
(def bilist-conditions-spec
  {:name 'nnrat/farkas-cross-bilist-conditions
   :kind :definition
   :universes []
   :type (function/arrow list-lower list-upper 'Prop)
   :value
   (function/lam
    [['lower-rows list-lower] ['upper-rows list-upper]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     lower-row
     (function/lam [['ignored list-lower]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head lower-row] ['tail list-lower] ['ih 'Prop]]
      (proposition/conjunction
       (crosses 'upper-rows (lo-a 'head) (lo-s 'head) (lo-w 'head))
       'ih))
     'lower-rows))})

(def definition-specs [lowers-satisfied-spec bilist-conditions-spec])

(def bilist-necessary-spec
  {:name 'nnrat/farkas-cross-bilist-necessary
   :universes []
   :type
   (function/forall
    [['lower-rows list-lower] ['upper-rows list-upper] ['v nnrat]
     ['lowers (lowers-satisfied 'lower-rows 'v)]
     ['uppers (uppers-satisfied 'upper-rows 'v)]]
    (bilist-conditions 'lower-rows 'upper-rows))
   :value
   (function/lam
    [['lower-rows list-lower] ['upper-rows list-upper] ['v nnrat]
     ['lowers (lowers-satisfied 'lower-rows 'v)]
     ['uppers (uppers-satisfied 'upper-rows 'v)]]
    (let [motive (function/lam
                  [['lrs list-lower]]
                  (function/arrow (lowers-satisfied 'lrs 'v)
                                  (bilist-conditions 'lrs 'upper-rows)))
          nil-case
          (function/lam
           [['hnil (lowers-satisfied
                    (function/app (function/const* 'data/nil [type-level])
                                  lower-row)
                    'v)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head lower-row] ['tail list-lower]
            ['ih (function/arrow (lowers-satisfied 'tail 'v)
                                 (bilist-conditions 'tail 'upper-rows))]]
           (function/lam
            [['hcons (lowers-satisfied
                      (function/app (function/const* 'data/cons [type-level])
                                    lower-row 'head 'tail)
                      'v)]]
            (let [head-lower (lower-at 'head 'v)
                  tail-prop (lowers-satisfied 'tail 'v)
                  head-lower-proof (left-conjunct head-lower tail-prop 'hcons)
                  tail-proof (right-conjunct head-lower tail-prop 'hcons)
                  head-crosses
                  (cross-list-necessary (lo-a 'head) (lo-s 'head) (lo-w 'head)
                                        'upper-rows 'v head-lower-proof 'uppers)]
              (conjoin (crosses 'upper-rows (lo-a 'head) (lo-s 'head)
                                (lo-w 'head))
                       (bilist-conditions 'tail 'upper-rows)
                       head-crosses
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        lower-row motive nil-case cons-case 'lower-rows)
       'lowers)))})

(def theorem-specs [bilist-necessary-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      cross-list/extend-environment
      (support/extend-with :nnrat-farkas-cross-bilist
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
