(ns rainbow.math.rational.signed.lp-duality-on
  "LP weak duality and the optimality certificate, quantified over the rows and
  columns an instance actually has.

  These are the same three theorems as `rainbow.math.rational.signed.lp-duality`, with
  every feasibility hypothesis stated as `signed/all-at-most` over the row or
  column LIST rather than over the whole index type. That is the difference
  between a theorem and a checker: on an index type like `data/Nat` a hypothesis
  `forall i : Nat, (Mx)_i <= b_i` is false for any real program, because the
  program has no eight-thousandth constraint. Only a finite index type escapes
  it, and fixing the index type fixes the instance size.

  With the list form, an instance of ANY size is checked by folding one decided
  comparison per row and per column -- work a generator emits in a loop -- and
  handing the resulting conjunctions to
  `optimization/signed-lp-optimality-certificate-on`.

  The proofs are the parametric ones with two substitutions: monotonicity through
  `signed/map-sum-monotone-on` instead of `signed/map-sum-monotone`, and the
  per-index bound lemmas carried across the list by
  `signed/all-at-most-combine` instead of being applied at an arbitrary index.
  Nothing about the mathematics changes; the quantifier does.

  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.lp-duality :as lp]
            [rainbow.math.rational.signed.pointwise-order :as pointwise]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))
(defn- all-at-most [A f g xs]
  (app (function/const* 'signed/all-at-most [U]) A f g xs))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))
(defn- signed-at-most-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- monotone-on [A f g xs dominated]
  (app (function/const* 'signed/map-sum-monotone-on [U]) A f g xs dominated))
(defn- combine [A f g p q r s xs step first second]
  (app (function/const* 'signed/all-at-most-combine [U])
       A f g p q r s xs step first second))

(def zero-family (function/lam [['ignored 'A]] signed-zero))
(def zero-family-b (function/lam [['ignored 'B]] signed-zero))

;; ---- double counting, on the listed indices ---------------------------------

(defn- term-at [T i j] (app (app T i) j))

(def ^:private column-family
  (function/lam [['j 'B]]
                (map-sum 'A (function/lam [['i 'A]] (term-at 'T 'i 'j)) 'is)))
(def ^:private row-family
  (function/lam [['i 'A]]
                (map-sum 'B (function/lam [['j 'B]] (term-at 'T 'i 'j)) 'js)))

(def double-counting-spec
  {:name 'optimization/signed-double-counting-weak-duality-on :universes ['u]
   :type
   (function/forall
    [['A type-u] ['B type-u]
     ['T (function/arrow 'A (function/arrow 'B signed))]
     ['primal (function/arrow 'B signed)] ['dual (function/arrow 'A signed)]
     ['is (list-of 'A)] ['js (list-of 'B)]
     ['column (all-at-most 'B 'primal column-family 'js)]
     ['row (all-at-most 'A row-family 'dual 'is)]]
    (sle (map-sum 'B 'primal 'js) (map-sum 'A 'dual 'is)))
   :value
   (function/lam
    [['A type-u] ['B type-u]
     ['T (function/arrow 'A (function/arrow 'B signed))]
     ['primal (function/arrow 'B signed)] ['dual (function/arrow 'A signed)]
     ['is (list-of 'A)] ['js (list-of 'B)]
     ['column (all-at-most 'B 'primal column-family 'js)]
     ['row (all-at-most 'A row-family 'dual 'is)]]
    (let [columns-total (map-sum 'B column-family 'js)
          rows-total (map-sum 'A row-family 'is)
          below-columns (monotone-on 'B 'primal column-family 'js 'column)
          rows-below (monotone-on 'A row-family 'dual 'is 'row)
          columns-below
          (signed-at-most-respects
           (map-sum 'B 'primal 'js) (map-sum 'B 'primal 'js)
           columns-total rows-total
           (signed-refl (map-sum 'B 'primal 'js))
           (signed-sym rows-total columns-total
                       (app (function/const* 'signed/map-sum-swap [U])
                            'A 'B 'T 'is 'js))
           below-columns)]
      (signed-at-most-transitive
       (map-sum 'B 'primal 'js) rows-total (map-sum 'A 'dual 'is)
       columns-below rows-below)))})

;; ---- the instance-shaped LP theorems ----------------------------------------

(defn- constraint-row [M x cols i]
  (map-sum 'B (function/lam [['j 'B]]
                            (smul (app (app M i) 'j) (app x 'j))) cols))

(defn- dual-column [M y rows j]
  (map-sum 'A (function/lam [['i 'A]]
                            (smul (app (app M 'i) j) (app y 'i))) rows))

(def matrix-type (function/arrow 'A (function/arrow 'B signed)))

(def ^:private row-activity-family
  (function/lam [['i 'A]] (constraint-row 'M 'x 'cols 'i)))
(def ^:private dual-price-family
  (function/lam [['j 'B]] (dual-column 'M 'y 'rows 'j)))
(def ^:private lp-term-family
  (function/lam
   [['i 'A]]
   (function/lam [['j 'B]]
                 (smul (smul (app (app 'M 'i) 'j) (app 'x 'j)) (app 'y 'i)))))

(defn- lp-bindings []
  [['A type-u] ['B type-u]
   ['M matrix-type]
   ['b (function/arrow 'A signed)]
   ['c (function/arrow 'B signed)]
   ['x (function/arrow 'B signed)]
   ['y (function/arrow 'A signed)]
   ['rows (list-of 'A)] ['cols (list-of 'B)]
   ['primal-feasible (all-at-most 'A row-activity-family 'b 'rows)]
   ['dual-feasible (all-at-most 'B 'c dual-price-family 'cols)]
   ['x-nonnegative (all-at-most 'B zero-family-b 'x 'cols)]
   ['y-nonnegative (all-at-most 'A zero-family 'y 'rows)]])

(def ^:private primal-objective
  (map-sum 'B (function/lam [['j 'B]] (smul (app 'c 'j) (app 'x 'j))) 'cols))
(def ^:private dual-objective
  (map-sum 'A (function/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i))) 'rows))

(def ^:private column-evidence
  (combine
   'B 'c dual-price-family zero-family-b 'x
   (function/lam [['j 'B]] (smul (app 'c 'j) (app 'x 'j)))
   (function/lam [['j 'B]]
                 (map-sum 'A (function/lam [['i 'A]]
                                           (app (app lp-term-family 'i) 'j))
                          'rows))
   'cols
   (function/lam
    [['j 'B]
     ['feasible (sle (app 'c 'j) (dual-column 'M 'y 'rows 'j))]
     ['nonnegative (sle signed-zero (app 'x 'j))]]
    (app (function/const* 'optimization/signed-lp-column-bound [U])
         'A
         (function/lam [['i 'A]] (app (app 'M 'i) 'j))
         'y (app 'x 'j) (app 'c 'j) 'rows 'feasible 'nonnegative))
   'dual-feasible 'x-nonnegative))

(def ^:private row-evidence
  (combine
   'A row-activity-family 'b zero-family 'y
   (function/lam [['i 'A]]
                 (map-sum 'B (function/lam [['j 'B]]
                                           (app (app lp-term-family 'i) 'j))
                          'cols))
   (function/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i)))
   'rows
   (function/lam
    [['i 'A]
     ['feasible (sle (constraint-row 'M 'x 'cols 'i) (app 'b 'i))]
     ['nonnegative (sle signed-zero (app 'y 'i))]]
    (app (function/const*
          'optimization/signed-row-bound-of-primal-feasibility [U])
         'B
         (function/lam [['j 'B]] (smul (app (app 'M 'i) 'j) (app 'x 'j)))
         (app 'b 'i) (app 'y 'i) 'cols 'feasible 'nonnegative))
   'primal-feasible 'y-nonnegative))

(def ^:private weak-duality-body
  (app (function/const*
        'optimization/signed-double-counting-weak-duality-on [U])
       'A 'B lp-term-family
       (function/lam [['j 'B]] (smul (app 'c 'j) (app 'x 'j)))
       (function/lam [['i 'A]] (smul (app 'b 'i) (app 'y 'i)))
       'rows 'cols column-evidence row-evidence))

(def weak-duality-spec
  {:name 'optimization/signed-lp-weak-duality-on :universes ['u]
   :type (function/forall (lp-bindings) (sle primal-objective dual-objective))
   :value (function/lam (lp-bindings) weak-duality-body)})

(def optimality-certificate-spec
  {:name 'optimization/signed-lp-optimality-certificate-on :universes ['u]
   :type
   (function/forall
    (into (lp-bindings)
          [['gap (seq-equiv dual-objective primal-objective)]
           ['candidate (function/arrow 'B signed)]
           ['candidate-feasible
            (all-at-most 'A
                         (function/lam [['i 'A]]
                                       (constraint-row 'M 'candidate 'cols 'i))
                         'b 'rows)]
           ['candidate-nonnegative
            (all-at-most 'B zero-family-b 'candidate 'cols)]])
    (sle (map-sum 'B (function/lam [['j 'B]]
                                   (smul (app 'c 'j) (app 'candidate 'j)))
                  'cols)
         primal-objective))
   :value
   (function/lam
    (into (lp-bindings)
          [['gap (seq-equiv dual-objective primal-objective)]
           ['candidate (function/arrow 'B signed)]
           ['candidate-feasible
            (all-at-most 'A
                         (function/lam [['i 'A]]
                                       (constraint-row 'M 'candidate 'cols 'i))
                         'b 'rows)]
           ['candidate-nonnegative
            (all-at-most 'B zero-family-b 'candidate 'cols)]])
    (let [candidate-objective
          (map-sum 'B (function/lam [['j 'B]]
                                    (smul (app 'c 'j) (app 'candidate 'j)))
                   'cols)]
      (signed-at-most-respects
       candidate-objective candidate-objective
       dual-objective primal-objective
       (signed-refl candidate-objective)
       'gap
       (app (function/const* 'optimization/signed-lp-weak-duality-on [U])
            'A 'B 'M 'b 'c 'candidate 'y 'rows 'cols
            'candidate-feasible 'dual-feasible
            'candidate-nonnegative 'y-nonnegative))))})

(def definition-specs [])
(def theorem-specs
  [double-counting-spec weak-duality-spec optimality-certificate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.lp-duality rainbow.math.rational.signed.pointwise-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-lp-duality-on theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.lp-duality-on))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
