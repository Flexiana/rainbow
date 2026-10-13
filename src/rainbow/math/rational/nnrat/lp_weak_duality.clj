(ns rainbow.math.rational.nnrat.lp-weak-duality
  "LP weak duality over nonnegative rationals -- the frontier-OR capstone:

    primal   max c.x   s.t. A x <= b, x >= 0        (x : cols -> nnrat)
    dual     min b.y   s.t. Aᵀy >= c, y >= 0        (y : rows -> nnrat)

    nnrat/lp-weak-duality :
      (forall i, (A x)_i <= b_i)       -- primal feasibility
      -> (forall j, c_j <= (Aᵀy)_j)    -- dual feasibility
      -> c.x <= b.y

  Nonnegativity of x, y is automatic (nnrat).  Dot products are map-sum over the
  index lists.  This is the verified, axiom-free weak-duality bound: any dual
  feasible objective bounds any primal feasible objective from above -- the
  soundness core of every LP relaxation / bound certificate in OR.

  Proof (all products in a fixed order, one per-term reorder):
    c.x = sum_j c_j x_j
        <= sum_j (Aᵀy)_j x_j                     [map-sum-monotone + multiply-right-monotone, dual feas]
        ~  sum_j sum_i (A_ij y_i) x_j             [map-sum-scale-right under map-sum-respects]
        ~  sum_i sum_j (A_ij y_i) x_j             [Fubini map-sum-swap]
        ~  sum_i sum_j (A_ij x_j) y_i             [per-term reorder: assoc+comm+mult-respects]
        ~  sum_i (A x)_i y_i                      [map-sum-scale-right backwards, under map-sum-respects]
        <= sum_i b_i y_i = b.y                    [map-sum-monotone + multiply-right-monotone, primal feas]
    the ~ chain bridged to <= by at-most-respects-equivalence + at-most-transitive.

  Native and axiom-free; chains the finite-sum toolkit (list-sum monotone,
  map-sum respects/scale-right, Fubini) plus multiply right-monotone/associative/
  commutative(standalone) and d63 multiply-respects/at-most-respects."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.list-sum :as ls]
            [rainbow.math.rational.nnrat.map-sum-respects :as mr]
            [rainbow.math.rational.nnrat.map-sum-scale :as sc]
            [rainbow.math.rational.nnrat.fubini :as fu]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as rm]
            [rainbow.math.rational.nnrat.product-reassociation :as pr]
            [rainbow.math.rational.nnrat.multiply-commute :as mc]))

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
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- app [f x] (function/app f x))
(defn- lam [v ty body] (function/lam [[v ty]] body))

(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-monotone [A f g hfg xs]
  (function/app (function/const* 'nnrat/map-sum-monotone [U]) A f g hfg xs))
(defn- map-sum-respects [A f g hfg xs]
  (function/app (function/const* 'nnrat/map-sum-respects-equivalence [U]) A f g hfg xs))
(defn- scale-right [A f c xs]
  (function/app (function/const* 'nnrat/map-sum-scale-right [U]) A f c xs))
(defn- swap [A B F is js]
  (function/app (function/const* 'nnrat/map-sum-swap [U]) A B F is js))
(defn- mul-right-monotone [a b c h]
  (function/app (function/const* 'nnrat/multiply-right-monotone []) a b c h))
(defn- mul-assoc [a b c] (function/app (function/const* 'nnrat/multiply-associative []) a b c))
(defn- mul-comm [a b] (function/app (function/const* 'nnrat/multiply-commutative []) a b))
(defn- mul-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence []) l le r re sl sr))
(defn- at-most-resp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- at-most-trans [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))

;; ((p*q)*r) ~ ((p*r)*q)
(defn- reorder [p q r]
  (equiv-trans (rmul (rmul p q) r) (rmul p (rmul q r)) (rmul (rmul p r) q)
               (mul-assoc p q r)
               (equiv-trans (rmul p (rmul q r)) (rmul p (rmul r q)) (rmul (rmul p r) q)
                            (mul-respects p p (rmul q r) (rmul r q) (equiv-refl p) (mul-comm q r))
                            (equiv-sym (rmul (rmul p r) q) (rmul p (rmul r q)) (mul-assoc p r q)))))

(def weak-duality-spec
  {:name 'nnrat/lp-weak-duality :universes ['u]
   :type (function/forall
          [['RowT type-u] ['ColT type-u]
           ['A (arrow 'RowT (arrow 'ColT nnrat))]
           ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
           ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
           ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
           ['hp (function/forall [['i 'RowT]]
                                 (rat-le (map-sum 'ColT (lam 'j 'ColT (rmul (app (app 'A 'i) 'j) (app 'x 'j))) 'cols)
                                         (app 'b 'i)))]
           ['hd (function/forall [['j 'ColT]]
                                 (rat-le (app 'c 'j)
                                         (map-sum 'RowT (lam 'i 'RowT (rmul (app (app 'A 'i) 'j) (app 'y 'i))) 'rows)))]]
          (rat-le (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols)
                  (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows)))
   :value
   (function/lam
    [['RowT type-u] ['ColT type-u]
     ['A (arrow 'RowT (arrow 'ColT nnrat))]
     ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
     ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
     ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
     ['hp (function/forall [['i 'RowT]]
                           (rat-le (map-sum 'ColT (lam 'j 'ColT (rmul (app (app 'A 'i) 'j) (app 'x 'j))) 'cols)
                                   (app 'b 'i)))]
     ['hd (function/forall [['j 'ColT]]
                           (rat-le (app 'c 'j)
                                   (map-sum 'RowT (lam 'i 'RowT (rmul (app (app 'A 'i) 'j) (app 'y 'i))) 'rows)))]]
    (let [Aij (fn [i j] (app (app 'A i) j))
          ;; row/col dot pieces
          Ax-body (fn [i] (map-sum 'ColT (lam 'j 'ColT (rmul (Aij i 'j) (app 'x 'j))) 'cols))
          ATy-body (fn [j] (map-sum 'RowT (lam 'i 'RowT (rmul (Aij 'i j) (app 'y 'i))) 'rows))
          cx (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols)
          by (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows)
          ;; objective mappings
          cx-map (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j)))
          aty-x-map (lam 'j 'ColT (rmul (ATy-body 'j) (app 'x 'j)))
          RHS1 (map-sum 'ColT aty-x-map 'cols)
          ;; gterm/hterm inner mappings
          g-inner (fn [j] (lam 'i 'RowT (rmul (rmul (Aij 'i j) (app 'y 'i)) (app 'x j))))
          h-inner (fn [i] (lam 'j 'ColT (rmul (rmul (Aij i 'j) (app 'x 'j)) (app 'y i))))
          DS1-map (lam 'j 'ColT (map-sum 'RowT (g-inner 'j) 'rows))
          DS1 (map-sum 'ColT DS1-map 'cols)
          ;; Fubini F : ColT -> RowT -> nnrat, F j i = (A_ij y_i) x_j
          Ffub (lam 'j 'ColT (lam 'i 'RowT (rmul (rmul (Aij 'i 'j) (app 'y 'i)) (app 'x 'j))))
          DS2-jmap (fn [i] (lam 'j 'ColT (rmul (rmul (Aij i 'j) (app 'y i)) (app 'x 'j))))
          DS2-map (lam 'i 'RowT (map-sum 'ColT (DS2-jmap 'i) 'cols))
          DS2 (map-sum 'RowT DS2-map 'rows)
          DS3-map (lam 'i 'RowT (map-sum 'ColT (h-inner 'i) 'cols))
          DS3 (map-sum 'RowT DS3-map 'rows)
          Axy-map (lam 'i 'RowT (rmul (Ax-body 'i) (app 'y 'i)))
          RHS5 (map-sum 'RowT Axy-map 'rows)

          ;; --- leg1 : cx <= RHS1 ---
          leg1 (map-sum-monotone 'ColT cx-map aty-x-map
                                 (lam 'j 'ColT
                                      (mul-right-monotone (app 'c 'j) (ATy-body 'j) (app 'x 'j) (app 'hd 'j)))
                                 'cols)
          ;; --- E2 : RHS1 ~ DS1  (per j: (ATy_j)*x_j ~ sum_i (A_ij y_i) x_j) ---
          e2 (map-sum-respects 'ColT aty-x-map DS1-map
                               (lam 'j 'ColT
                                    (scale-right 'RowT (lam 'i 'RowT (rmul (Aij 'i 'j) (app 'y 'i))) (app 'x 'j) 'rows))
                               'cols)
          ;; --- F3 : DS1 ~ DS2 (Fubini) ---
          f3 (swap 'ColT 'RowT Ffub 'cols 'rows)
          ;; --- E4 : DS2 ~ DS3 (per i, per j reorder) ---
          e4 (map-sum-respects 'RowT DS2-map DS3-map
                               (lam 'i 'RowT
                                    (map-sum-respects 'ColT (DS2-jmap 'i) (h-inner 'i)
                                                      (lam 'j 'ColT (reorder (Aij 'i 'j) (app 'y 'i) (app 'x 'j)))
                                                      'cols))
                               'rows)
          ;; --- E5 : DS3 ~ RHS5 (per i: sum_j (A_ij x_j) y_i ~ (Ax_i) y_i) ---
          e5 (map-sum-respects 'RowT DS3-map Axy-map
                               (lam 'i 'RowT
                                    (equiv-sym (rmul (Ax-body 'i) (app 'y 'i))
                                               (map-sum 'ColT (h-inner 'i) 'cols)
                                               (scale-right 'ColT (lam 'j 'ColT (rmul (Aij 'i 'j) (app 'x 'j))) (app 'y 'i) 'cols)))
                               'rows)
          ;; --- leg2 : RHS5 <= by ---
          leg2 (map-sum-monotone 'RowT Axy-map (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i)))
                                 (lam 'i 'RowT
                                      (mul-right-monotone (Ax-body 'i) (app 'b 'i) (app 'y 'i) (app 'hp 'i)))
                                 'rows)
          ;; chain the equivalences RHS1 ~ RHS5
          eq-1-2 e2
          eq-1-3 (equiv-trans RHS1 DS1 DS2 eq-1-2 f3)
          eq-1-4 (equiv-trans RHS1 DS2 DS3 eq-1-3 e4)
          eq-1-5 (equiv-trans RHS1 DS3 RHS5 eq-1-4 e5)
          ;; cx <= RHS1 ~ RHS5  =>  cx <= RHS5
          cx-le-rhs5 (at-most-resp cx cx RHS5 RHS1 (equiv-refl cx)
                                   (equiv-sym RHS1 RHS5 eq-1-5) leg1)]
      ;; cx <= RHS5 <= by
      (at-most-trans cx RHS5 by cx-le-rhs5 leg2)))})

(def definition-specs [])
(def theorem-specs [weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.list-sum rainbow.math.rational.nnrat.map-sum-respects rainbow.math.rational.nnrat.map-sum-scale rainbow.math.rational.nnrat.fubini rainbow.math.rational.nnrat.multiply-right-monotone rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-lp-weak-duality (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.lp-weak-duality))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
