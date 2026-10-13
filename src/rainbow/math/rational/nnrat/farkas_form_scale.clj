(ns rainbow.math.rational.nnrat.farkas-form-scale
  "The unified representation, brick 2 core:
  scaling a linear form scales its coefficient vector.

  The columnwise cross transform's arithmetic: crossing a lower row against
  an upper row multiplies one row's tail linear form by the other's head
  coefficient (e.g. eval(U_tail)*L_1). nnrat/farkas-form-scale-right proves
  eval(pairs) * c ~ eval(scale-right c pairs), where nnrat/farkas-scale-right
  multiplies each coefficient by c (the variables unchanged). So the cross's
  product terms ARE linear forms over the same tail variables with scaled
  coefficient vectors -- the bookkeeping that lets the reduced constraint be
  read as a coefficient vector over the remaining variables. Proof: List.rec
  over the pairs; nil by multiply-zero-left; cons by distribute-right then
  multiply-swap-right (fold the scalar into the coefficient) then the IH.
  Native proof data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.farkas-linear-form :as linear-form]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def pair-nn
  (function/app (function/const* 'data/Product [type-level type-level]) nnrat nnrat))
(def list-pair
  (function/app (function/const* 'data/List [type-level]) pair-nn))

(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- mul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(def zero (function/const* 'nnrat/zero []))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- fst [v]
  (function/app (function/const* 'product/first [type-level type-level]) nnrat nnrat v))
(defn- snd [v]
  (function/app (function/const* 'product/second [type-level type-level]) nnrat nnrat v))
(defn- pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level]) nnrat nnrat x y))
(defn- cons-pair [h t]
  (function/app (function/const* 'data/cons [type-level]) pair-nn h t))
(defn- nil-pair []
  (function/app (function/const* 'data/nil [type-level]) pair-nn))
(defn- eval-form [pairs]
  (function/app (function/const* 'nnrat/linear-form []) pairs))
(defn- scale-right [c pairs]
  (function/app (function/const* 'nnrat/farkas-scale-right []) c pairs))

(defn- erefl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- etrans [l m r a b]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r a b))
(defn- add-respects [l le r re sl sr]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l le r re sl sr))
(defn- distribute-right [a b m]
  (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(defn- swap-right [a b c]
  (function/app (function/const* 'nnrat/multiply-swap-right []) a b c))
(defn- multiply-zero-left [x]
  (function/app (function/const* 'nnrat/multiply-zero-left []) x))

;; scale a coefficient vector: multiply each coefficient by c
(def scale-right-spec
  {:name 'nnrat/farkas-scale-right
   :kind :definition
   :universes []
   :type (function/arrow nnrat list-pair list-pair)
   :value
   (function/lam
    [['c nnrat] ['pairs list-pair]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     pair-nn
     (function/lam [['ignored list-pair]] list-pair)
     (nil-pair)
     (function/lam
      [['head pair-nn] ['tail list-pair] ['ih list-pair]]
      (cons-pair (pair (mul (fst 'head) 'c) (snd 'head)) 'ih))
     'pairs))})

(def definition-specs [scale-right-spec])

(def form-scale-right-spec
  {:name 'nnrat/farkas-form-scale-right
   :universes []
   :type
   (function/forall
    [['c nnrat] ['pairs list-pair]]
    (equiv (mul (eval-form 'pairs) 'c) (eval-form (scale-right 'c 'pairs))))
   :value
   (function/lam
    [['c nnrat] ['pairs list-pair]]
    (function/app
     (function/const* 'data/List.rec [type-level zero-level])
     pair-nn
     (function/lam
      [['ps list-pair]]
      (equiv (mul (eval-form 'ps) 'c) (eval-form (scale-right 'c 'ps))))
     ;; nil: (eval nil)*c = 0*c ~ 0 = eval (scale nil)
     (multiply-zero-left 'c)
     ;; cons head tail
     (function/lam
      [['head pair-nn] ['tail list-pair]
       ['ih (equiv (mul (eval-form 'tail) 'c)
                   (eval-form (scale-right 'c 'tail)))]]
      (let [cv (mul (fst 'head) (snd 'head))         ; coeff*var
            cvc (mul cv 'c)                          ; (coeff*var)*c
            ccv (mul (mul (fst 'head) 'c) (snd 'head)) ; (coeff*c)*var
            tail-c (mul (eval-form 'tail) 'c)
            scaled-tail (eval-form (scale-right 'c 'tail))]
        ;; (cv + eval tail)*c ~ cv*c + (eval tail)*c
        (etrans (mul (add cv (eval-form 'tail)) 'c)
                (add cvc tail-c)
                (add ccv scaled-tail)
                (distribute-right cv (eval-form 'tail) 'c)
                ;; cv*c ~ (coeff*c)*var  and  (eval tail)*c ~ scaled-tail (ih)
                (add-respects cvc ccv tail-c scaled-tail
                              (swap-right (fst 'head) (snd 'head) 'c)
                              'ih))))
     'pairs))})

(def theorem-specs [form-scale-right-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.identities rainbow.math.rational.nnrat.farkas-linear-form])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-form-scale (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-form-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
