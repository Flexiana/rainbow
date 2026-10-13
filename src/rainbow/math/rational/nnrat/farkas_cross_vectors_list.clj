(ns rainbow.math.rational.nnrat.farkas-cross-vectors-list
  "Brick 3 per-pair fold: cross one
  lower coefficient-vector constraint against a LIST of upper
  coefficient-vector constraints.

  Each upper constraint is (coefficient, tail-vector, bound), meaning
  eval(cons (coeff, x1) tail) <= bound at the eliminated variable x1. Given
  a lower constraint b_L <= eval(cons (l-coeff, x1) l-tail) and every upper
  constraint holding at x1, every pairwise reduced constraint holds
  (nnrat/farkas-cross-vectors-reduced-holds): each is
    b_L*u_coeff + eval(scale l-coeff u-tail) <= bound*l-coeff + eval(scale u_coeff l-tail),
  a both-sides coefficient-vector constraint over the tail. By List.rec
  applying nnrat/farkas-cross-vectors per upper. The full n-variable round
  maps this over the lower list too (a second List.rec); this is the
  one-lower core. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-cross-vectors :as cross]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def list-pair (function/app (function/const* 'data/List [type-level]) pair-nn))
(def tb (product list-pair nnrat))               ; (tail-vector, bound)
(def uconstraint (product nnrat tb))             ; (coeff, (tail, bound))
(def list-u (function/app (function/const* 'data/List [type-level]) uconstraint))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- mk-pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
;; upper-constraint field extractors
(defn- uc-coeff [r] (fst nnrat tb r))
(defn- uc-tail [r] (fst list-pair nnrat (snd nnrat tb r)))
(defn- uc-bnd [r] (snd list-pair nnrat (snd nnrat tb r)))

;; the upper constraint holds at x1: eval(cons (coeff,x1) tail) <= bound
(defn- upper-holds [r x1]
  (at-most (eval-form (cons-pair (mk-pair (uc-coeff r) x1) (uc-tail r)))
           (uc-bnd r)))
;; the reduced both-sides vector constraint for this (lower, upper) pair
(defn- reduced-at [r x1 l-coeff l-tail b-l]
  (at-most (add (mul b-l (uc-coeff r)) (eval-form (scale-right l-coeff (uc-tail r))))
           (add (mul (uc-bnd r) l-coeff) (eval-form (scale-right (uc-coeff r) l-tail)))))

(defn- uppers-hold [uppers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold [])
                uppers x1))
(defn- reduced-conds [uppers x1 l-coeff l-tail b-l]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced [])
                uppers x1 l-coeff l-tail b-l))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))
(defn- cross-vectors [x1 l-coeff u-coeff l-tail u-tail b-l b-u lower upper]
  (function/app (function/const* 'nnrat/farkas-cross-vectors [])
                x1 l-coeff u-coeff l-tail u-tail b-l b-u lower upper))

(def uppers-hold-spec
  {:name 'nnrat/farkas-cross-vectors-uppers-hold
   :kind :definition
   :universes []
   :type (function/arrow list-u nnrat 'Prop)
   :value
   (function/lam
    [['uppers list-u] ['x1 nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     uconstraint
     (function/lam [['ignored list-u]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head uconstraint] ['tail list-u] ['ih 'Prop]]
      (proposition/conjunction (upper-holds 'head 'x1) 'ih))
     'uppers))})

(def reduced-spec
  {:name 'nnrat/farkas-cross-vectors-reduced
   :kind :definition
   :universes []
   :type (function/arrow list-u nnrat nnrat list-pair nnrat 'Prop)
   :value
   (function/lam
    [['uppers list-u] ['x1 nnrat] ['l-coeff nnrat] ['l-tail list-pair]
     ['b-l nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     uconstraint
     (function/lam [['ignored list-u]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head uconstraint] ['tail list-u] ['ih 'Prop]]
      (proposition/conjunction
       (reduced-at 'head 'x1 'l-coeff 'l-tail 'b-l) 'ih))
     'uppers))})

(def definition-specs [uppers-hold-spec reduced-spec])

(def cross-vectors-list-spec
  {:name 'nnrat/farkas-cross-vectors-reduced-holds
   :universes []
   :type
   (function/forall
    [['x1 nnrat] ['l-coeff nnrat] ['l-tail list-pair] ['b-l nnrat]
     ['uppers list-u]
     ['lower (at-most 'b-l (eval-form (cons-pair (mk-pair 'l-coeff 'x1) 'l-tail)))]
     ['uh (uppers-hold 'uppers 'x1)]]
    (reduced-conds 'uppers 'x1 'l-coeff 'l-tail 'b-l))
   :value
   (function/lam
    [['x1 nnrat] ['l-coeff nnrat] ['l-tail list-pair] ['b-l nnrat]
     ['uppers list-u]
     ['lower (at-most 'b-l (eval-form (cons-pair (mk-pair 'l-coeff 'x1) 'l-tail)))]
     ['uh (uppers-hold 'uppers 'x1)]]
    (let [motive (function/lam
                  [['us list-u]]
                  (function/arrow (uppers-hold 'us 'x1)
                                  (reduced-conds 'us 'x1 'l-coeff 'l-tail 'b-l)))
          nil-case
          (function/lam
           [['hnil (uppers-hold
                    (function/app (function/const* 'data/nil [type-level])
                                  uconstraint)
                    'x1)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head uconstraint] ['tail list-u]
            ['ih (function/arrow (uppers-hold 'tail 'x1)
                                 (reduced-conds 'tail 'x1 'l-coeff 'l-tail 'b-l))]]
           (function/lam
            [['hcons (uppers-hold
                      (function/app (function/const* 'data/cons [type-level])
                                    uconstraint 'head 'tail)
                      'x1)]]
            (let [head-prop (upper-holds 'head 'x1)
                  tail-prop (uppers-hold 'tail 'x1)
                  head-proof (left-conjunct head-prop tail-prop 'hcons)
                  tail-proof (right-conjunct head-prop tail-prop 'hcons)
                  head-reduced
                  (cross-vectors 'x1 'l-coeff (uc-coeff 'head) 'l-tail
                                 (uc-tail 'head) 'b-l (uc-bnd 'head)
                                 'lower head-proof)]
              (conjoin (reduced-at 'head 'x1 'l-coeff 'l-tail 'b-l)
                       (reduced-conds 'tail 'x1 'l-coeff 'l-tail 'b-l)
                       head-reduced
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        uconstraint motive nil-case cons-case 'uppers)
       'uh)))})

(def theorem-specs [cross-vectors-list-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-cross-vectors])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-cross-vectors-list (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-cross-vectors-list))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
