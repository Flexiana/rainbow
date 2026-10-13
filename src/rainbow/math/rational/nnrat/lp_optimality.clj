(ns rainbow.math.rational.nnrat.lp-optimality
  "LP optimality certificate over nonnegative rationals -- the sellable corollary
  of weak duality: a matching feasible primal/dual pair PROVES optimality.

    nnrat/lp-optimality-certificate :
      (forall i, (A x)_i <= b_i)      -- x primal feasible
      -> (forall j, c_j <= (Aᵀy)_j)   -- y dual feasible
      -> c.x ~ b.y                    -- zero duality gap (matching objectives)
      -> (forall x', (forall i, (A x')_i <= b_i) -> c.x' <= c.x)

  i.e. any primal-feasible x whose objective matches some dual-feasible y's
  objective is a maximizer of c.x over all primal-feasible points -- the
  optimality certificate every LP solver emits, here machine-checked.  Proof: for
  any other feasible x', weak duality gives c.x' <= b.y, and the zero-gap
  hypothesis rewrites b.y to c.x (at-most-respects-equivalence).  Native and
  axiom-free; chains nnrat-lp-weak-duality on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.lp-weak-duality :as lp]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element] (function/app (function/const* 'data/List [data-level]) element))
(defn- arrow [a b] (function/arrow a b))
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- rat-le [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- at-most-resp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- app [f x] (function/app f x))
(defn- lam [v ty body] (function/lam [[v ty]] body))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- weak-duality [RowT ColT A b c x y rows cols hp hd]
  (function/app (function/const* 'nnrat/lp-weak-duality [U]) RowT ColT A b c x y rows cols hp hd))

;; the dot products / feasibility predicates, written exactly as in lp-weak-duality
(defn- Ax-row [A x cols i] (map-sum 'ColT (lam 'j 'ColT (rmul (app (app A i) 'j) (app x 'j))) cols))
(defn- primal-feasible [A x b cols]
  (function/forall [['i 'RowT]] (rat-le (Ax-row A x cols 'i) (app b 'i))))
(defn- dual-feasible [A c y rows]
  (function/forall [['j 'ColT]]
                   (rat-le (app c 'j)
                           (map-sum 'RowT (lam 'i 'RowT (rmul (app (app A 'i) 'j) (app y 'i))) rows))))
(defn- cdotx [c x cols] (map-sum 'ColT (lam 'j 'ColT (rmul (app c 'j) (app x 'j))) cols))
(defn- bdoty [b y rows] (map-sum 'RowT (lam 'i 'RowT (rmul (app b 'i) (app y 'i))) rows))

(def optimality-spec
  {:name 'nnrat/lp-optimality-certificate :universes ['u]
   :type (function/forall
          [['RowT type-u] ['ColT type-u]
           ['A (arrow 'RowT (arrow 'ColT nnrat))]
           ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
           ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
           ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
           ['hp (primal-feasible 'A 'x 'b 'cols)]
           ['hd (dual-feasible 'A 'c 'y 'rows)]
           ['hgap (equiv (cdotx 'c 'x 'cols) (bdoty 'b 'y 'rows))]
           ['x-alt (arrow 'ColT nnrat)]
           ['hp-alt (primal-feasible 'A 'x-alt 'b 'cols)]]
          (rat-le (cdotx 'c 'x-alt 'cols) (cdotx 'c 'x 'cols)))
   :value
   (function/lam
    [['RowT type-u] ['ColT type-u]
     ['A (arrow 'RowT (arrow 'ColT nnrat))]
     ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
     ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
     ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
     ['hp (primal-feasible 'A 'x 'b 'cols)]
     ['hd (dual-feasible 'A 'c 'y 'rows)]
     ['hgap (equiv (cdotx 'c 'x 'cols) (bdoty 'b 'y 'rows))]
     ['x-alt (arrow 'ColT nnrat)]
     ['hp-alt (primal-feasible 'A 'x-alt 'b 'cols)]]
    (let [cx  (cdotx 'c 'x 'cols)
          cx' (cdotx 'c 'x-alt 'cols)
          by  (bdoty 'b 'y 'rows)
          ;; weak duality on the ALTERNATIVE primal x-alt and the given dual y : c.x' <= b.y
          wd (weak-duality 'RowT 'ColT 'A 'b 'c 'x-alt 'y 'rows 'cols 'hp-alt 'hd)]
      ;; at-most-respects-equivalence: ordered is on the EQUIVALENT versions
      ;; (cx' <= by) with same-left cx'~cx', same-right cx~by (=hgap) => cx' <= cx
      (at-most-resp cx' cx' cx by
                    (equiv-refl cx')
                    'hgap                     ; c.x ~ b.y
                    wd)))})

;; dual optimality: symmetric -- a matching pair proves the DUAL y is optimal
;; (minimizes b.y over dual-feasible points)
(def dual-optimality-spec
  {:name 'nnrat/lp-dual-optimality-certificate :universes ['u]
   :type (function/forall
          [['RowT type-u] ['ColT type-u]
           ['A (arrow 'RowT (arrow 'ColT nnrat))]
           ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
           ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
           ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
           ['hp (primal-feasible 'A 'x 'b 'cols)]
           ['hd (dual-feasible 'A 'c 'y 'rows)]
           ['hgap (equiv (cdotx 'c 'x 'cols) (bdoty 'b 'y 'rows))]
           ['y-alt (arrow 'RowT nnrat)]
           ['hd-alt (dual-feasible 'A 'c 'y-alt 'rows)]]
          (rat-le (bdoty 'b 'y 'rows) (bdoty 'b 'y-alt 'rows)))
   :value
   (function/lam
    [['RowT type-u] ['ColT type-u]
     ['A (arrow 'RowT (arrow 'ColT nnrat))]
     ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
     ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
     ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
     ['hp (primal-feasible 'A 'x 'b 'cols)]
     ['hd (dual-feasible 'A 'c 'y 'rows)]
     ['hgap (equiv (cdotx 'c 'x 'cols) (bdoty 'b 'y 'rows))]
     ['y-alt (arrow 'RowT nnrat)]
     ['hd-alt (dual-feasible 'A 'c 'y-alt 'rows)]]
    (let [cx  (cdotx 'c 'x 'cols)
          by  (bdoty 'b 'y 'rows)
          by' (bdoty 'b 'y-alt 'rows)
          ;; weak duality on the given primal x and the ALTERNATIVE dual y-alt : c.x <= b.y'
          wd (weak-duality 'RowT 'ColT 'A 'b 'c 'x 'y-alt 'rows 'cols 'hp 'hd-alt)]
      ;; b.y ~ c.x <= b.y'  =>  b.y <= b.y'
      (at-most-resp by cx by' by'
                    (equiv-sym cx by 'hgap)   ; b.y ~ c.x
                    (equiv-refl by')
                    wd)))})

(def definition-specs [])
(def theorem-specs [optimality-spec dual-optimality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      lp/extend-environment
      (support/extend-with :nnrat-lp-optimality
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
