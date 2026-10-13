(ns rainbow.math.rational.nnrat.farkas-cross-vectors
  "The unified representation, brick 3 core:
  one elimination cross at the coefficient-vector level.

  Crossing a lower constraint b_L <= eval(L) against an upper constraint
  eval(U) <= b_U -- both coefficient vectors whose head pair is the variable
  x1 being eliminated -- yields the reduced constraint over the tail
  variables directly in coefficient-vector form:

    b_L*U_1 + eval(scale L_1 U_tail)  <=  b_U*L_1 + eval(scale U_1 L_tail).

  nnrat/farkas-cross-vectors proves it by composing three proved theorems:
  head-split each constraint on x1 (nnrat/linear-form-lower-split /
  -upper-split) to expose the current coefficient and the tail block, apply
  the affine cross crux (nnrat/farkas-affine-cross-necessary), then rewrite
  the product terms as scaled coefficient vectors
  (nnrat/farkas-reduced-vector). This is the round's arithmetic at the
  representation level: two coefficient-vector constraints in one fewer
  variable produce a both-sides coefficient-vector constraint. The fold over
  the variable count applies this per (lower, upper) pair, then head-splits
  and both-sides-reduces the next variable. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-affine-cross :as cross]
            [rainbow.math.rational.nnrat.farkas-reduced-vector :as reduced]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nn
  (function/app (function/const* 'data/Product [type-level type-level]) nnrat nnrat))
(def list-pair
  (function/app (function/const* 'data/List [type-level]) pair-nn))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- eval-form [pairs]
  (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
(defn- pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- lower-split [w p tail h]
  (function/app (function/const* 'nnrat/linear-form-lower-split []) w p tail h))
(defn- upper-split [p tail b h]
  (function/app (function/const* 'nnrat/linear-form-upper-split []) p tail b h))
(defn- affine-cross [a-lo a-hi w-lo s-lo s-hi b-hi v lower upper]
  (function/app (function/const* 'nnrat/farkas-affine-cross-necessary [])
                a-lo a-hi w-lo s-lo s-hi b-hi v lower upper))
(defn- reduced-vector [w-lo a-hi a-lo b-hi l-tail u-tail cross]
  (function/app (function/const* 'nnrat/farkas-reduced-vector [])
                w-lo a-hi a-lo b-hi l-tail u-tail cross))

(def cross-vectors-spec
  {:name 'nnrat/farkas-cross-vectors
   :universes []
   :type
   (function/forall
    [['x1 nnrat] ['l-coeff nnrat] ['u-coeff nnrat]
     ['l-tail list-pair] ['u-tail list-pair] ['b-l nnrat] ['b-u nnrat]
     ['lower (at-most 'b-l (eval-form (cons-pair (pair 'l-coeff 'x1) 'l-tail)))]
     ['upper (at-most (eval-form (cons-pair (pair 'u-coeff 'x1) 'u-tail)) 'b-u)]]
    (at-most
     (add (mul 'b-l 'u-coeff) (eval-form (scale-right 'l-coeff 'u-tail)))
     (add (mul 'b-u 'l-coeff) (eval-form (scale-right 'u-coeff 'l-tail)))))
   :value
   (function/lam
    [['x1 nnrat] ['l-coeff nnrat] ['u-coeff nnrat]
     ['l-tail list-pair] ['u-tail list-pair] ['b-l nnrat] ['b-u nnrat]
     ['lower (at-most 'b-l (eval-form (cons-pair (pair 'l-coeff 'x1) 'l-tail)))]
     ['upper (at-most (eval-form (cons-pair (pair 'u-coeff 'x1) 'u-tail)) 'b-u)]]
    (let [;; head-split exposes the x1 coefficient and the tail block
          lo (lower-split 'b-l (pair 'l-coeff 'x1) 'l-tail 'lower)
          up (upper-split (pair 'u-coeff 'x1) 'u-tail 'b-u 'upper)
          ;; the affine cross crux eliminates x1
          crossed (affine-cross 'l-coeff 'u-coeff 'b-l
                                (eval-form 'l-tail) (eval-form 'u-tail) 'b-u
                                'x1 lo up)]
      ;; rewrite the product terms as scaled coefficient vectors
      (reduced-vector 'b-l 'u-coeff 'l-coeff 'b-u 'l-tail 'u-tail crossed)))})

(def definition-specs [])
(def theorem-specs [cross-vectors-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      cross/extend-environment
      reduced/extend-environment
      (support/extend-with :nnrat-farkas-cross-vectors
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
