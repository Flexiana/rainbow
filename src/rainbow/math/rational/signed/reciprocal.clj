(ns rainbow.math.rational.signed.reciprocal
  "The signed-rational reciprocal operation and its self-inverse law -- the missing
  field operation. This completes the signed rationals as a field (up to ~) and is the
  gate for all signed division, including the limit-quotient law.

    signed/reciprocal x := x * (1 / (x*x))          [sign-free: 1/x = x/x^2]
    signed/multiply-reciprocal-self :
      1 <= numerator (magnitude (x*x)) -> x * (reciprocal x) ~ one

  The definition is sign-free BY CONSTRUCTION: instead of a signum case-split, it uses
  1/x = x/x^2. Since x*x is always nonnegative (signed/square-nonnegative), its magnitude
  is a genuine nnrat and admits the make(succ p, q)-form reciprocal, so no reciprocal-
  respects lemma is needed. The nonzero hypothesis is `1 <= numerator (magnitude (x*x))`
  (equivalently x !~ 0): exactly the positive-numerator shape nnrat divide-self-positive
  and make-succ-of-positive-numerator consume.

  Proof of self-inverse:  x*(x*R) ~ (x*x)*R           [multiply-associative]
                                 ~ from-nnrat D * R    [x*x ~ from-nnrat D, from-nnrat-magnitude]
                                 ~ from-nnrat (D * recip mmag)   [from-nnrat-multiply]
                                 ~ from-nnrat one ~ one [D ~ mmag then divide-self-positive]
  where D = magnitude (x*x), mmag = make (succ (pred (num D))) (den-pred D), R = from-nnrat
  (recip mmag). Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.geometric-bridge :as geometric-bridge]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]
            [rainbow.math.rational.signed.magnitude :as magnitude]
            [rainbow.math.rational.nnrat.positive-succ-form :as succ-form]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]
            [rainbow.math.rational.division :as division]
            [rainbow.math.nonnegative-rational :as nnrat-base]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private one (function/const* 'signed/one []))
(def ^:private nnone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- mk [num dp] (app (function/const* 'data/pair [tl tl]) nat nat num dp))
(defn- nrecip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- rmul [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- reciprocal [x] (app (function/const* 'signed/reciprocal []) x))
;; mmag D = make (succ (pred (num D))) (den-pred D)
(defn- mmag-of-D [D] (mk (succ (pred* (numr D))) (denpred D)))
;; theorem wrappers
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mult-assoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- fnn-magn [x h] (app (function/const* 'signed/from-nnrat-magnitude []) x h))
(defn- square-nn [x] (app (function/const* 'signed/square-nonnegative []) x))
(defn- fnn-mul [l r] (app (function/const* 'signed/from-nnrat-multiply []) l r))
(defn- fnn-resp [l r h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) l r h))
(defn- nn-mult-resp [l l' r r' hl hr]
  (app (function/const* 'nnrat/multiply-respects-equivalence []) l l' r r' hl hr))
(defn- nn-eqv-tr [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- nn-refl [x] (app (function/const* 'nnrat/equivalent-reflexive []) x))
(defn- make-succ [c h] (app (function/const* 'nnrat/make-succ-of-positive-numerator []) c h))
(defn- divide-self-pos [p q] (app (function/const* 'nnrat/divide-self-positive []) p q))

(def reciprocal-spec
  {:name 'signed/reciprocal
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow signed signed)
   :value (function/lam [['x signed]]
                        (smul 'x (fnn (nrecip (mmag-of-D (mag (smul 'x 'x)))))))})

(def multiply-reciprocal-self-spec
  {:name 'signed/multiply-reciprocal-self
   :universes []
   :type (function/forall
          [['x signed] ['h (nat-le (succ zero) (numr (mag (smul 'x 'x))))]]
          (seqv (smul 'x (reciprocal 'x)) one))
   :value
   (function/lam
    [['x signed] ['h (nat-le (succ zero) (numr (mag (smul 'x 'x))))]]
    (let [sq (smul 'x 'x)
          D (mag sq)
          p (pred* (numr D))
          q (denpred D)
          mmag (mk (succ p) q)
          Rq (nrecip mmag)
          R (fnn Rq)
          ;; nnrat self-inverse:  D * recip mmag ~ 1
          Dmmag (make-succ D 'h)                             ; D ~ mmag
          selfinv (nn-eqv-tr (rmul D Rq) (rmul mmag Rq) nnone
                             (nn-mult-resp D mmag Rq Rq Dmmag (nn-refl Rq))
                             (divide-self-pos p q))          ; D*Rq ~ mmag*Rq ~ 1
          ;; signed chain:  x*(x*R) ~ (x*x)*R ~ (fnn D)*R ~ fnn(D*Rq) ~ fnn one ~ one
          stepA (eqv-sym (smul sq R) (smul 'x (smul 'x R)) (mult-assoc 'x 'x R))
          stepB (mrre sq (fnn D) R (fnn-magn sq (square-nn 'x)))
          stepC (fnn-mul D Rq)                               ; (fnn D)*(fnn Rq) ~ fnn(D*Rq)
          stepD (fnn-resp (rmul D Rq) nnone selfinv)]        ; fnn(D*Rq) ~ fnn one (=def one)
      (eqv-tr (smul 'x (smul 'x R)) (smul sq R) one stepA
              (eqv-tr (smul sq R) (smul (fnn D) R) one stepB
                      (eqv-tr (smul (fnn D) R) (fnn (rmul D Rq)) one stepC stepD)))))})

(def theorem-specs [reciprocal-spec multiply-reciprocal-self-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.vector.norm-nonnegative rainbow.math.rational.signed.magnitude rainbow.math.rational.nnrat.positive-succ-form rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.division rainbow.math.nonnegative-rational])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-reciprocal theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.reciprocal))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
