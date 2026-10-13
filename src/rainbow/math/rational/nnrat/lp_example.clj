(ns rainbow.math.rational.nnrat.lp-example
  "A concrete, fully worked LP with a machine-checked optimality certificate --
  the tangible 'sellable' artifact: a real optimization instance whose proposed
  solution is PROVEN optimal by the kernel, with no trust in any solver.

  Instance (indices = Bool, so 2 constraints and 2 variables; rows=cols=[true,false]):
      maximize  c.x = x_0 + x_1
      s.t.      x_0 + x_1 <= 2   (both constraints identical, A = all ones)
                x >= 0
  Proposed primal  x = (1, 1)  (objective 2);  dual  y = (1, 0)  (objective 2).
  y is dual feasible (A^T y = (1,1) >= c = (1,1)) and the objectives match
  (c.x = 2 = b.y), a zero duality gap -- so by lp-optimality-certificate x is a
  maximizer.

    nnrat/lp-example-x-optimal :
      forall x' : Bool -> nnrat,
        (forall i, (A x')_i <= b_i)  ->  c.x' <= 2

  i.e. no feasible point beats x's objective of 2.  Numbers are chosen so every
  feasibility/gap check reduces to reflexivity (y=(1,0) keeps arithmetic integral).
  Native and axiom-free; instantiates nnrat/lp-optimality-certificate."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.lp-optimality :as opt]))

(def zero-level [:zero])
(def type-level [:succ [:zero]])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def tt (function/const* 'data/true []))
(def ff (function/const* 'data/false []))
(def one (function/const* 'nnrat/one []))
(def rzero (function/const* 'nnrat/zero []))
(defn- make [n dp]
  (function/app (function/const* 'nnrat/make [])
                (nth (iterate #(function/app (function/const* 'data/succ []) %)
                              (function/const* 'data/zero [])) n)
                (nth (iterate #(function/app (function/const* 'data/succ []) %)
                              (function/const* 'data/zero [])) dp)))
(def two (make 2 0))

(defn- app [f x] (function/app f x))
(defn- lam [v ty body] (function/lam [[v ty]] body))
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- rat-le [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- at-most-refl [v] (function/app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- cons-b [h t] (function/app (function/const* 'data/cons [type-level]) bool h t))
(def nil-b (function/app (function/const* 'data/nil [type-level]) bool))
(defn- map-sum [f xs] (function/app (function/const* 'nnrat/map-sum [zero-level]) bool f xs))
(defn- bool-rec-prop [motive false-case true-case d]
  (function/app (function/const* 'data/Bool.rec [[:zero]]) motive false-case true-case d))
(defn- bool-rec-nnrat [motive false-case true-case d]
  (function/app (function/const* 'data/Bool.rec [type-level]) motive false-case true-case d))

;; instance data
(def A (lam 'i bool (lam 'j bool one)))            ; A i j = 1
(def bvec (lam 'i bool two))                        ; b_i = 2
(def cvec (lam 'j bool one))                        ; c_j = 1
(def xvec (lam 'j bool one))                        ; x_j = 1
(def yvec (lam 'i bool                              ; y = (true->1, false->0)
              (bool-rec-nnrat (lam 'ig bool nnrat) rzero one 'i)))
(def rows (cons-b tt (cons-b ff nil-b)))
(def cols rows)

(defn- Ax-row [i] (map-sum (lam 'j bool (rmul (app (app A i) 'j) (app xvec 'j))) cols))
(defn- ATy-col [j] (map-sum (lam 'i bool (rmul (app (app A 'i) j) (app yvec 'i))) rows))
(def cx (map-sum (lam 'j bool (rmul (app cvec 'j) (app xvec 'j))) cols))
(def by (map-sum (lam 'i bool (rmul (app bvec 'i) (app yvec 'i))) rows))

;; primal feasibility: forall i, (A x)_i <= b_i  (both reduce to 2 <= 2)
(def hp
  (lam 'i bool
       (bool-rec-prop (lam 'iv bool (rat-le (Ax-row 'iv) (app bvec 'iv)))
                      (at-most-refl two) (at-most-refl two) 'i)))
;; dual feasibility: forall j, c_j <= (A^T y)_j  (both reduce to 1 <= 1)
(def hd
  (lam 'j bool
       (bool-rec-prop (lam 'jv bool (rat-le (app cvec 'jv) (ATy-col 'jv)))
                      (at-most-refl one) (at-most-refl one) 'j)))
;; zero gap: c.x ~ b.y  (both reduce to 2)
(def hgap (equiv-refl two))

(def x-optimal-spec
  {:name 'nnrat/lp-example-x-optimal :universes []
   :type (function/forall
          [['x-alt (function/arrow bool nnrat)]
           ['hp-alt (function/forall [['i bool]]
                                     (rat-le (map-sum (lam 'j bool (rmul (app (app A 'i) 'j) (app 'x-alt 'j))) cols)
                                             (app bvec 'i)))]]
          (rat-le (map-sum (lam 'j bool (rmul (app cvec 'j) (app 'x-alt 'j))) cols) two))
   :value
   (function/lam
    [['x-alt (function/arrow bool nnrat)]
     ['hp-alt (function/forall [['i bool]]
                               (rat-le (map-sum (lam 'j bool (rmul (app (app A 'i) 'j) (app 'x-alt 'j))) cols)
                                       (app bvec 'i)))]]
    (function/app (function/const* 'nnrat/lp-optimality-certificate [zero-level])
                  bool bool A bvec cvec xvec yvec rows cols hp hd hgap 'x-alt 'hp-alt))})

(def definition-specs [])
(def theorem-specs [x-optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      opt/extend-environment
      (support/extend-with :nnrat-lp-example
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
