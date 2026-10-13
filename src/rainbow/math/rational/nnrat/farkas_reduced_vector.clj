(ns rainbow.math.rational.nnrat.farkas-reduced-vector
  "The unified representation, brick 2 assembly
 : the cross condition expressed as a
  both-sides constraint over transformed coefficient vectors.

  Crossing a lower row (tail vector L_tail, head coefficient a_lo, bound
  w_lo) against an upper row (tail vector U_tail, head coefficient a_hi,
  bound b_hi) gives the cross condition
    w_lo*a_hi + eval(U_tail)*a_lo <= b_hi*a_lo + eval(L_tail)*a_hi.
  nnrat/farkas-reduced-vector rewrites its variable parts as coefficient
  vectors, using the scale lemma (nnrat/farkas-form-scale-right) on each
  side: eval(U_tail)*a_lo ~ eval(scale a_lo U_tail) and eval(L_tail)*a_hi ~
  eval(scale a_hi L_tail). So the reduced constraint is
    w_lo*a_hi + eval(scale a_lo U_tail) <= b_hi*a_lo + eval(scale a_hi L_tail)
  -- a both-sides LINEAR constraint over the tail variables whose two
  coefficient vectors are scale(a_lo, U_tail) and scale(a_hi, L_tail). This
  is the columnwise cross transform assembled: the reduced constraint is
  back in the coefficient-vector representation over one fewer variable
  (head-splitting the next variable off these vectors, then the both-sides
  reduction, is the next round). Transported by at-most-respects. Native
  proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-form-scale :as scale]))

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
(defn- form-scale [c pairs]
  (function/app (function/const* 'nnrat/farkas-form-scale-right []) c pairs))
(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- esym [l r same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- at-most-respects [l el r er sl sr ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                l el r er sl sr ordered))

(def reduced-vector-spec
  {:name 'nnrat/farkas-reduced-vector
   :universes []
   :type
   (function/forall
    [['w-lo nnrat] ['a-hi nnrat] ['a-lo nnrat] ['b-hi nnrat]
     ['l-tail list-pair] ['u-tail list-pair]
     ['cross (at-most
              (add (mul 'w-lo 'a-hi) (mul (eval-form 'u-tail) 'a-lo))
              (add (mul 'b-hi 'a-lo) (mul (eval-form 'l-tail) 'a-hi)))]]
    (at-most
     (add (mul 'w-lo 'a-hi) (eval-form (scale-right 'a-lo 'u-tail)))
     (add (mul 'b-hi 'a-lo) (eval-form (scale-right 'a-hi 'l-tail)))))
   :value
   (function/lam
    [['w-lo nnrat] ['a-hi nnrat] ['a-lo nnrat] ['b-hi nnrat]
     ['l-tail list-pair] ['u-tail list-pair]
     ['cross (at-most
              (add (mul 'w-lo 'a-hi) (mul (eval-form 'u-tail) 'a-lo))
              (add (mul 'b-hi 'a-lo) (mul (eval-form 'l-tail) 'a-hi)))]]
    (let [wa (mul 'w-lo 'a-hi)
          ba (mul 'b-hi 'a-lo)
          u-prod (mul (eval-form 'u-tail) 'a-lo)
          l-prod (mul (eval-form 'l-tail) 'a-hi)
          u-scaled (eval-form (scale-right 'a-lo 'u-tail))
          l-scaled (eval-form (scale-right 'a-hi 'l-tail))
          old-lhs (add wa u-prod)
          old-rhs (add ba l-prod)
          new-lhs (add wa u-scaled)
          new-rhs (add ba l-scaled)
          ;; old-lhs ~ new-lhs  (scale the U-tail product term)
          lhs-eq (add-respects wa wa u-prod u-scaled (erefl wa)
                               (form-scale 'a-lo 'u-tail))
          ;; old-rhs ~ new-rhs  (scale the L-tail product term)
          rhs-eq (add-respects ba ba l-prod l-scaled (erefl ba)
                               (form-scale 'a-hi 'l-tail))]
      (at-most-respects
       new-lhs old-lhs new-rhs old-rhs
       (esym old-lhs new-lhs lhs-eq)
       (esym old-rhs new-rhs rhs-eq)
       'cross)))})

(def definition-specs [])
(def theorem-specs [reduced-vector-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      scale/extend-environment
      (support/extend-with :nnrat-farkas-reduced-vector
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
