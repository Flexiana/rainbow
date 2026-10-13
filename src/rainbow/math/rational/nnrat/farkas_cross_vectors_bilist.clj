(ns rainbow.math.rational.nnrat.farkas-cross-vectors-bilist
  "Brick 3 full round: cross a LIST of
  lower coefficient-vector constraints against a LIST of upper
  coefficient-vector constraints -- the whole round's reduced set.

  Given a list of lower constraints and a list of upper constraints (each
  (coefficient, tail-vector, bound)), all holding at the eliminated variable
  x1, every pairwise reduced both-sides vector constraint holds
  (nnrat/farkas-cross-vectors-all-reduced): for each lower row, its whole
  per-upper reduced list (brick 3's one-lower fold
  nnrat/farkas-cross-vectors-reduced-holds), collected across the lower list
  by a second List.rec. This is one full elimination round expressed on the
  coefficient-vector representation: two constraint lists in n variables
  produce the pairwise reduced both-sides constraints over n-1 variables --
  the coefficient-vector analogue of brick 6's cross-product core. The
  over-variable recursion folds this (partition + head-split feed the next
  round); the base case grounds it. Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.farkas-cross-vectors-list :as vlist]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- product [a b]
  (function/app (function/const* 'data/Product [type-level type-level]) a b))
(def pair-nn (product nnrat nnrat))
(def list-pair (function/app (function/const* 'data/List [type-level]) pair-nn))
(def tb (product list-pair nnrat))
(def constraint (product nnrat tb))              ; (coeff, (tail, bound))
(def list-c (function/app (function/const* 'data/List [type-level]) constraint))

(defn- at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- eval-form [pairs] (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- fst [a b v]
  (function/app (function/const* 'product/first [type-level type-level]) a b v))
(defn- snd [a b v]
  (function/app (function/const* 'product/second [type-level type-level]) a b v))
(defn- mk-pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- lc-coeff [r] (fst nnrat tb r))
(defn- lc-tail [r] (fst list-pair nnrat (snd nnrat tb r)))
(defn- lc-bnd [r] (snd list-pair nnrat (snd nnrat tb r)))

;; a lower constraint holds at x1: bound <= eval(cons (coeff,x1) tail)
(defn- lower-holds [r x1]
  (at-most (lc-bnd r)
           (eval-form (cons-pair (mk-pair (lc-coeff r) x1) (lc-tail r)))))
(defn- uppers-hold [uppers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-uppers-hold [])
                uppers x1))
(defn- reduced-conds [uppers x1 l-coeff l-tail b-l]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced [])
                uppers x1 l-coeff l-tail b-l))
(defn- reduced-holds [x1 l-coeff l-tail b-l uppers lower uh]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-reduced-holds [])
                x1 l-coeff l-tail b-l uppers lower uh))

(defn- lowers-hold [lowers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-lowers-hold [])
                lowers x1))
(defn- all-reduced [lowers uppers x1]
  (function/app (function/const* 'nnrat/farkas-cross-vectors-all-reduced-conds [])
                lowers uppers x1))

(defn- conjoin [l r lp rp]
  (function/app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- left-conjunct [l r both]
  (function/app (function/const* 'proposition/left []) l r both))
(defn- right-conjunct [l r both]
  (function/app (function/const* 'proposition/right []) l r both))

(def lowers-hold-spec
  {:name 'nnrat/farkas-cross-vectors-lowers-hold
   :kind :definition
   :universes []
   :type (function/arrow list-c nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-c] ['x1 nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     constraint
     (function/lam [['ignored list-c]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head constraint] ['tail list-c] ['ih 'Prop]]
      (proposition/conjunction (lower-holds 'head 'x1) 'ih))
     'lowers))})

(def all-reduced-spec
  {:name 'nnrat/farkas-cross-vectors-all-reduced-conds
   :kind :definition
   :universes []
   :type (function/arrow list-c list-c nnrat 'Prop)
   :value
   (function/lam
    [['lowers list-c] ['uppers list-c] ['x1 nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     constraint
     (function/lam [['ignored list-c]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head constraint] ['tail list-c] ['ih 'Prop]]
      (proposition/conjunction
       (reduced-conds 'uppers 'x1 (lc-coeff 'head) (lc-tail 'head) (lc-bnd 'head))
       'ih))
     'lowers))})

(def definition-specs [lowers-hold-spec all-reduced-spec])

(def all-reduced-necessary-spec
  {:name 'nnrat/farkas-cross-vectors-all-reduced
   :universes []
   :type
   (function/forall
    [['lowers list-c] ['uppers list-c] ['x1 nnrat]
     ['lh (lowers-hold 'lowers 'x1)]
     ['uh (uppers-hold 'uppers 'x1)]]
    (all-reduced 'lowers 'uppers 'x1))
   :value
   (function/lam
    [['lowers list-c] ['uppers list-c] ['x1 nnrat]
     ['lh (lowers-hold 'lowers 'x1)]
     ['uh (uppers-hold 'uppers 'x1)]]
    (let [motive (function/lam
                  [['ls list-c]]
                  (function/arrow (lowers-hold 'ls 'x1)
                                  (all-reduced 'ls 'uppers 'x1)))
          nil-case
          (function/lam
           [['hnil (lowers-hold
                    (function/app (function/const* 'data/nil [type-level])
                                  constraint)
                    'x1)]]
           (function/const* 'proposition/trivial []))
          cons-case
          (function/lam
           [['head constraint] ['tail list-c]
            ['ih (function/arrow (lowers-hold 'tail 'x1)
                                 (all-reduced 'tail 'uppers 'x1))]]
           (function/lam
            [['hcons (lowers-hold
                      (function/app (function/const* 'data/cons [type-level])
                                    constraint 'head 'tail)
                      'x1)]]
            (let [head-prop (lower-holds 'head 'x1)
                  tail-prop (lowers-hold 'tail 'x1)
                  head-proof (left-conjunct head-prop tail-prop 'hcons)
                  tail-proof (right-conjunct head-prop tail-prop 'hcons)
                  head-reduced
                  (reduced-holds 'x1 (lc-coeff 'head) (lc-tail 'head)
                                 (lc-bnd 'head) 'uppers head-proof 'uh)]
              (conjoin (reduced-conds 'uppers 'x1 (lc-coeff 'head)
                                      (lc-tail 'head) (lc-bnd 'head))
                       (all-reduced 'tail 'uppers 'x1)
                       head-reduced
                       (function/app 'ih tail-proof)))))]
      (function/app
       (function/app
        (function/const* 'data/List.rec [type-level zero-level])
        constraint motive nil-case cons-case 'lowers)
       'lh)))})

(def theorem-specs [all-reduced-necessary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-cross-vectors-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-cross-vectors-bilist (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-cross-vectors-bilist))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
