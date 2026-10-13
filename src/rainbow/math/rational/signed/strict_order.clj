(ns rainbow.math.rational.signed.strict-order
  "Strict order on signed rationals -- the foundation strict convexity (and unique-minimizer
  results) need, which the non-strict `signed/at-most` lane lacked.

    signed/less-than x y := (at-most x y) AND (not (equivalent x y))    [reducible]
    signed/less-than-intro            : at-most x y -> not(x~y) -> x<y
    signed/less-than-implies-at-most  : x<y -> at-most x y
    signed/less-than-irreflexive      : not (x<x)
    signed/less-than-asymmetric       : x<y -> not (y<x)

  Built on the intuitionistic-logic layer (proposition/conjunction, /negation = P->falsity,
  /conjoin, /left, /right) plus at-most-antisymmetric and equivalent-reflexive. Irreflexivity
  feeds x~x (reflexivity) to the negation component; asymmetry derives x~y from at-most both
  ways (antisymmetry) and contradicts the negation component. Transitivity and strict
  monotonicity are the next bricks. Wall-free; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- antisym [a b ab ba] (app (function/const* 'signed/at-most-antisymmetric []) a b ab ba))
(defn- pconj [l r] (app (function/const* 'proposition/conjunction []) l r))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(defn- pconjoin [l r le re] (app (function/const* 'proposition/conjoin []) l r le re))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- lt [x y] (app (function/const* 'signed/less-than []) x y))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-resp [a ah b bh hab hbb hord] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh hab hbb hord))
(def ^:private prop 'Prop)
;; z <= x  from  x ~ z  (transport x<=x along x~z on the left)
(defn- le-of-equiv-rev [x z exz] (le-resp x z x x exz (erefl x) (le-refl x)))
(defn- lt-le [x y h] (pleft (sle x y) (pneg (seqv x y)) h))   ; x<y -> x<=y
(defn- lt-neq [x y h] (pright (sle x y) (pneg (seqv x y)) h)) ; x<y -> (x~y)->falsity

(def less-than-spec
  {:name 'signed/less-than
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow signed (function/arrow signed prop))
   :value (function/lam [['x signed] ['y signed]]
                        (pconj (sle 'x 'y) (pneg (seqv 'x 'y))))})

(def less-than-intro-spec
  {:name 'signed/less-than-intro
   :universes []
   :type (function/forall
          [['x signed] ['y signed]
           ['le (sle 'x 'y)] ['neq (pneg (seqv 'x 'y))]]
          (lt 'x 'y))
   :value (function/lam
           [['x signed] ['y signed]
            ['le (sle 'x 'y)] ['neq (pneg (seqv 'x 'y))]]
           (pconjoin (sle 'x 'y) (pneg (seqv 'x 'y)) 'le 'neq))})

(def less-than-implies-at-most-spec
  {:name 'signed/less-than-implies-at-most
   :universes []
   :type (function/forall [['x signed] ['y signed] ['h (lt 'x 'y)]] (sle 'x 'y))
   :value (function/lam [['x signed] ['y signed] ['h (lt 'x 'y)]]
                        (pleft (sle 'x 'y) (pneg (seqv 'x 'y)) 'h))})

(def less-than-irreflexive-spec
  {:name 'signed/less-than-irreflexive
   :universes []
   :type (function/forall [['x signed]] (pneg (lt 'x 'x)))
   :value (function/lam [['x signed]]
                        (function/lam [['h (lt 'x 'x)]]
                                      (app (pright (sle 'x 'x) (pneg (seqv 'x 'x)) 'h)
                                           (erefl 'x))))})

(def less-than-asymmetric-spec
  {:name 'signed/less-than-asymmetric
   :universes []
   :type (function/forall [['x signed] ['y signed] ['hxy (lt 'x 'y)]] (pneg (lt 'y 'x)))
   :value (function/lam
           [['x signed] ['y signed] ['hxy (lt 'x 'y)]]
           (function/lam
            [['hyx (lt 'y 'x)]]
            (app (pright (sle 'x 'y) (pneg (seqv 'x 'y)) 'hxy)      ; (x~y) -> falsity
                 (antisym 'x 'y
                          (pleft (sle 'x 'y) (pneg (seqv 'x 'y)) 'hxy)   ; x<=y
                          (pleft (sle 'y 'x) (pneg (seqv 'y 'x)) 'hyx)))))})  ; y<=x  => x~y

(def less-than-transitive-spec
  {:name 'signed/less-than-transitive
   :universes []
   :type (function/forall [['x signed] ['y signed] ['z signed]
                           ['hxy (lt 'x 'y)] ['hyz (lt 'y 'z)]]
                          (lt 'x 'z))
   :value (function/lam
           [['x signed] ['y signed] ['z signed]
            ['hxy (lt 'x 'y)] ['hyz (lt 'y 'z)]]
           (pconjoin (sle 'x 'z) (pneg (seqv 'x 'z))
                     (le-trans 'x 'y 'z (lt-le 'x 'y 'hxy) (lt-le 'y 'z 'hyz))
                     (function/lam
                      [['exz (seqv 'x 'z)]]
                      ;; x~z, x<=y, y<=z => x~y, contradicting hxy's not(x~y)
                      (app (lt-neq 'x 'y 'hxy)
                           (antisym 'x 'y (lt-le 'x 'y 'hxy)
                                    (le-trans 'y 'z 'x (lt-le 'y 'z 'hyz)
                                              (le-of-equiv-rev 'x 'z 'exz)))))))})

(def less-than-of-at-most-of-less-than-spec
  {:name 'signed/less-than-of-at-most-of-less-than
   :universes []
   :type (function/forall [['x signed] ['y signed] ['z signed]
                           ['hle (sle 'x 'y)] ['hyz (lt 'y 'z)]]
                          (lt 'x 'z))
   :value (function/lam
           [['x signed] ['y signed] ['z signed]
            ['hle (sle 'x 'y)] ['hyz (lt 'y 'z)]]
           (pconjoin (sle 'x 'z) (pneg (seqv 'x 'z))
                     (le-trans 'x 'y 'z 'hle (lt-le 'y 'z 'hyz))
                     (function/lam
                      [['exz (seqv 'x 'z)]]
                      ;; x~z, x<=y, y<=z => y~z, contradicting hyz's not(y~z)
                      (app (lt-neq 'y 'z 'hyz)
                           (antisym 'y 'z (lt-le 'y 'z 'hyz)
                                    (le-trans 'z 'x 'y (le-of-equiv-rev 'x 'z 'exz) 'hle))))))})

(def less-than-of-less-than-of-at-most-spec
  {:name 'signed/less-than-of-less-than-of-at-most
   :universes []
   :type (function/forall [['x signed] ['y signed] ['z signed]
                           ['hxy (lt 'x 'y)] ['hle (sle 'y 'z)]]
                          (lt 'x 'z))
   :value (function/lam
           [['x signed] ['y signed] ['z signed]
            ['hxy (lt 'x 'y)] ['hle (sle 'y 'z)]]
           (pconjoin (sle 'x 'z) (pneg (seqv 'x 'z))
                     (le-trans 'x 'y 'z (lt-le 'x 'y 'hxy) 'hle)
                     (function/lam
                      [['exz (seqv 'x 'z)]]
                      ;; x~z, x<=y, y<=z => x~y, contradicting hxy's not(x~y)
                      (app (lt-neq 'x 'y 'hxy)
                           (antisym 'x 'y (lt-le 'x 'y 'hxy)
                                    (le-trans 'y 'z 'x 'hle (le-of-equiv-rev 'x 'z 'exz)))))))})

(def theorem-specs
  [less-than-spec less-than-intro-spec less-than-implies-at-most-spec
   less-than-irreflexive-spec less-than-asymmetric-spec
   less-than-transitive-spec less-than-of-at-most-of-less-than-spec
   less-than-of-less-than-of-at-most-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.order-respects])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-strict-order theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.strict-order))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
