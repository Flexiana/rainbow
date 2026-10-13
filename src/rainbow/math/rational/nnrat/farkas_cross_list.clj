(ns rainbow.math.rational.nnrat.farkas-cross-list
  "Brick 5d-i of the general LP strong-duality Fourier-Motzkin encoding
 : the cross-product of one affine
  lower row against a LIST of affine upper rows.

  Eliminating a variable v that is bounded below by a single affine row
  (w_lo <= a_lo*v + s_lo -- the objective-boundary row in the two-variable
  case) and above by a list of affine upper rows (a_hi*v + s_hi <= b_hi --
  the primal rows, brick 4's row type). Any v satisfying the lower row and
  every upper row yields, for EVERY upper row, that row's cross condition
  (brick 5c, nnrat/farkas-affine-cross-necessary): the reduced system in
  the surviving variables. This maps the single-pair cross crux across the
  upper-row list by List.rec, exactly as brick 4's projection mapped its
  per-row argument.

  The reduced conditions are collected by nnrat/farkas-cross-list-conditions
  (a fold of the per-row cross condition), and
  nnrat/farkas-cross-list-necessary proves feasibility implies they all
  hold. Reuses brick 4's rows-satisfied fold for the uppers and brick 5c
  for each pair. Native proof data, axiom-free. The n-lower generalization
  (a list of lowers too) is brick 6's induction; the two-variable payoff
  needs only this one-lower form."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-affine-cross :as cross]
            [rainbow.math.rational.nnrat.farkas-elim-affine-list :as affine-list]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nnrat
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))
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
;; brick 4's upper coupling, a_hi*v + s_hi <= b_hi
(defn- upper-at [r value]
  (at-most (add (multiply (row-a r) value) (row-s r)) (row-b r)))
;; the cross condition for this upper row against the fixed lower row:
;; w_lo*a_hi + s_hi*a_lo <= b_hi*a_lo + s_lo*a_hi
(defn- cross-at [r a-lo s-lo w-lo]
  (at-most (add (multiply w-lo (row-a r)) (multiply (row-s r) a-lo))
           (add (multiply (row-b r) a-lo) (multiply s-lo (row-a r)))))

(defn- rows-satisfied [rows value]
  (function/app (function/const* 'nnrat/farkas-elim-affine-rows-satisfied [])
                rows value))
(defn- crosses [rows a-lo s-lo w-lo]
  (function/app (function/const* 'nnrat/farkas-cross-list-conditions [])
                rows a-lo s-lo w-lo))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))
(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))
(defn- affine-cross [a-lo a-hi w-lo s-lo s-hi b-hi v lower upper]
  (function/app (function/const* 'nnrat/farkas-affine-cross-necessary [])
                a-lo a-hi w-lo s-lo s-hi b-hi v lower upper))

;; The reduced cross conditions: one per upper row, folded by conjunction.
(def cross-conditions-spec
  {:name 'nnrat/farkas-cross-list-conditions
   :kind :definition
   :universes []
   :type (function/arrow list-row nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['rows list-row] ['a-lo nnrat] ['s-lo nnrat] ['w-lo nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     row
     (function/lam [['ignored list-row]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head row] ['tail list-row] ['ih 'Prop]]
      (proposition/conjunction (cross-at 'head 'a-lo 's-lo 'w-lo) 'ih))
     'rows))})

(def definition-specs [cross-conditions-spec])

(def cross-list-necessary-spec
  {:name 'nnrat/farkas-cross-list-necessary
   :universes []
   :type
   (function/forall
    [['a-lo nnrat] ['s-lo nnrat] ['w-lo nnrat]
     ['upper-rows list-row] ['v nnrat]
     ['lower (at-most 'w-lo (add (multiply 'a-lo 'v) 's-lo))]
     ['uppers (rows-satisfied 'upper-rows 'v)]]
    (crosses 'upper-rows 'a-lo 's-lo 'w-lo))
   :value
   (function/lam
    [['a-lo nnrat] ['s-lo nnrat] ['w-lo nnrat]
     ['upper-rows list-row] ['v nnrat]
     ['lower (at-most 'w-lo (add (multiply 'a-lo 'v) 's-lo))]
     ['uppers (rows-satisfied 'upper-rows 'v)]]
    (let [motive (function/lam
                  [['rs list-row]]
                  (function/arrow (rows-satisfied 'rs 'v)
                                  (crosses 'rs 'a-lo 's-lo 'w-lo)))
          nil-case
          (function/lam
           [['hnil (rows-satisfied
                    (function/app (function/const* 'data/nil [type-level]) row)
                    'v)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head row] ['tail list-row]
            ['ih (function/arrow (rows-satisfied 'tail 'v)
                                 (crosses 'tail 'a-lo 's-lo 'w-lo))]]
           (function/lam
            [['hcons (rows-satisfied
                      (function/app (function/const* 'data/cons [type-level])
                                    row 'head 'tail)
                      'v)]]
            (let [head-upper (upper-at 'head 'v)
                  tail-prop (rows-satisfied 'tail 'v)
                  head-upper-proof (left-conjunct head-upper tail-prop 'hcons)
                  tail-proof (right-conjunct head-upper tail-prop 'hcons)
                  head-cross
                  (affine-cross 'a-lo (row-a 'head) 'w-lo 's-lo
                                (row-s 'head) (row-b 'head) 'v
                                'lower head-upper-proof)]
              (conjoin (cross-at 'head 'a-lo 's-lo 'w-lo)
                       (crosses 'tail 'a-lo 's-lo 'w-lo)
                       head-cross
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        row motive nil-case cons-case 'upper-rows)
       'uppers)))})

(def theorem-specs [cross-list-necessary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-affine-cross rainbow.math.rational.nnrat.farkas-elim-affine-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-cross-list (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-cross-list))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
