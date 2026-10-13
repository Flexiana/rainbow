(ns rainbow.math.rational.nnrat.lp-complementary
  "Complementary slackness for LP over nonnegative rationals -- the KKT optimality
  characterization, now a named machine-checked theorem.

  With subtraction-free feasibility (primal (A x)_i + s_i ~ b_i, dual
  c_j + r_j ~ (Aᵀy)_j) and a ZERO duality gap (b.y ~ c.x):

    nnrat/lp-complementary-slackness-dual   : sum_j r_j x_j ~ 0
    nnrat/lp-complementary-slackness-primal : sum_i s_i y_i ~ 0

  i.e. at a zero-gap (hence optimal) primal/dual pair the total reduced-cost*value
  and slack*multiplier sums vanish; since each product is nonnegative,
  map-sum-zero-at-split then forces every individual r_e x_e and s_e y_e to 0 (a
  variable is 0 or its constraint is tight).  Proof: the gap-decomposition gives
  b.y ~ c.x + (SR + SS); zero gap + add-cancel-to-zero forces (SR + SS) ~ 0;
  add-zero-split splits it to SR ~ 0 and SS ~ 0.  (Per-term extraction to any
  individual r_e x_e ~ 0 is nnrat/map-sum-zero-at-split, in nnrat-map-sum-zero.)
  Native and axiom-free; chains nnrat-lp-gap and nnrat-add-cancel-zero on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.lp-gap :as gap]
            [rainbow.math.rational.nnrat.add-cancel-zero :as cz]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element] (function/app (function/const* 'data/List [data-level]) element))
(defn- arrow [a b] (function/arrow a b))
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- app [f x] (function/app f x))
(defn- lam [v ty body] (function/lam [[v ty]] body))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- gap-decomp [RowT ColT A b c x y s r rows cols hp hd]
  (function/app (function/const* 'nnrat/lp-gap-decomposition [U])
                RowT ColT A b c x y s r rows cols hp hd))
(defn- add-cancel-to-zero [a g h]
  (function/app (function/const* 'nnrat/add-cancel-to-zero []) a g h))
(defn- split-left [a b h] (function/app (function/const* 'nnrat/add-zero-split-left []) a b h))
(defn- split-right [a b h] (function/app (function/const* 'nnrat/add-zero-split-right []) a b h))

;; shared binder list for the LP setup + zero-gap hypothesis
(defn- setup-binders []
  [['RowT type-u] ['ColT type-u]
   ['A (arrow 'RowT (arrow 'ColT nnrat))]
   ['b (arrow 'RowT nnrat)] ['c (arrow 'ColT nnrat)]
   ['x (arrow 'ColT nnrat)] ['y (arrow 'RowT nnrat)]
   ['s (arrow 'RowT nnrat)] ['r (arrow 'ColT nnrat)]
   ['rows (list-of 'RowT)] ['cols (list-of 'ColT)]
   ['hp (function/forall [['i 'RowT]]
                         (equiv (radd (map-sum 'ColT (lam 'j 'ColT (rmul (app (app 'A 'i) 'j) (app 'x 'j))) 'cols)
                                      (app 's 'i))
                                (app 'b 'i)))]
   ['hd (function/forall [['j 'ColT]]
                         (equiv (radd (app 'c 'j) (app 'r 'j))
                                (map-sum 'RowT (lam 'i 'RowT (rmul (app (app 'A 'i) 'j) (app 'y 'i))) 'rows)))]
   ['hgap (equiv (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows)
                 (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols))]])

;; SR = sum_j r_j x_j ; SS = sum_i s_i y_i ; the two total slack sums vanish
(defn- SR [] (map-sum 'ColT (lam 'j 'ColT (rmul (app 'r 'j) (app 'x 'j))) 'cols))
(defn- SS [] (map-sum 'RowT (lam 'i 'RowT (rmul (app 's 'i) (app 'y 'i))) 'rows))
(defn- cx [] (map-sum 'ColT (lam 'j 'ColT (rmul (app 'c 'j) (app 'x 'j))) 'cols))
(defn- by [] (map-sum 'RowT (lam 'i 'RowT (rmul (app 'b 'i) (app 'y 'i))) 'rows))

;; G ~ 0 where G = SR + SS, from gap-decomposition + zero gap + add-cancel-to-zero
(defn- gap-sum-zero []
  (let [G (radd (SR) (SS))
        gd (gap-decomp 'RowT 'ColT 'A 'b 'c 'x 'y 's 'r 'rows 'cols 'hp 'hd) ; by ~ cx + G
        cxG-eq (equiv-trans (radd (cx) G) (by) (cx)
                            (equiv-sym (by) (radd (cx) G) gd) 'hgap)]        ; (cx + G) ~ cx
    (add-cancel-to-zero (cx) G cxG-eq)))                                     ; G ~ 0

(def cs-dual-spec
  {:name 'nnrat/lp-complementary-slackness-dual :universes ['u]
   :type (function/forall (setup-binders) (equiv (SR) nnrat-zero))
   :value (function/lam (setup-binders) (split-left (SR) (SS) (gap-sum-zero)))})

(def cs-primal-spec
  {:name 'nnrat/lp-complementary-slackness-primal :universes ['u]
   :type (function/forall (setup-binders) (equiv (SS) nnrat-zero))
   :value (function/lam (setup-binders) (split-right (SR) (SS) (gap-sum-zero)))})

(def definition-specs [])
(def theorem-specs [cs-dual-spec cs-primal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      gap/extend-environment
      cz/extend-environment
      (support/extend-with :nnrat-lp-complementary
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
