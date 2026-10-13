(ns rainbow.math.rational.nnrat.farkas-affine-cross
  "Brick 5c full of the general LP strong-duality Fourier-Motzkin encoding
 : the affine cross-elimination crux
  WITH COEFFICIENTS -- the coefficient wrapper around the additive core.

  Eliminating v bounded below by a coefficient-bearing affine row and above
  by another: from w_lo <= a_lo*v + s_lo (lower) and a_hi*v + s_hi <= b_hi
  (upper), the survivor condition (v eliminated) is
  w_lo*a_hi + s_hi*a_lo <= b_hi*a_lo + s_lo*a_hi -- the subtraction-free
  cross condition obtained by cross-multiplying the two rows by each other's
  coefficient. Necessary (certificate) direction; positivity-free.

  The proof REUSES the additive core
  (nnrat/farkas-additive-cross-necessary): scale the lower row on the right
  by a_hi and the upper by a_lo (multiply-right-monotone), distribute
  (multiply-distributes-add-right) so each becomes an additive row whose
  variable term is a triple product, align the two triple products
  D1 = (a_lo*v)*a_hi ~ (a_hi*v)*a_lo = D2 (multiply-swap-right +
  multiply-commutative through multiply-respects-equivalence), then hand the
  two additive rows to the core. This is the last new proof obligation of
  brick 5c; 5d lifts it to row lists and wires the objective. Native proof
  data, axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-additive-cross :as core]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as right-monotone]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- erefl [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- esym [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- etrans [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- mul-right-monotone [a b c ordered]
  (function/app (function/const* 'nnrat/multiply-right-monotone []) a b c ordered))
(defn- distribute-right [a b m]
  (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(defn- mul-swap-right [a b c]
  (function/app (function/const* 'nnrat/multiply-swap-right []) a b c))
(defn- mul-commutative [a b]
  (function/app (function/const* 'nnrat/multiply-commutative []) a b))
(defn- mul-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- add-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- at-most-respects [left eq-left right eq-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left eq-left right eq-right same-left same-right ordered))
(defn- additive-cross [w s-lo s-hi b v lower upper]
  (function/app (function/const* 'nnrat/farkas-additive-cross-necessary [])
                w s-lo s-hi b v lower upper))

(def affine-cross-necessary-spec
  {:name 'nnrat/farkas-affine-cross-necessary
   :universes []
   :type
   (function/forall
    [['a-lo nnrat] ['a-hi nnrat] ['w-lo nnrat] ['s-lo nnrat]
     ['s-hi nnrat] ['b-hi nnrat] ['v nnrat]
     ['lower (at-most 'w-lo (add (mul 'a-lo 'v) 's-lo))]
     ['upper (at-most (add (mul 'a-hi 'v) 's-hi) 'b-hi)]]
    (at-most (add (mul 'w-lo 'a-hi) (mul 's-hi 'a-lo))
             (add (mul 'b-hi 'a-lo) (mul 's-lo 'a-hi))))
   :value
   (function/lam
    [['a-lo nnrat] ['a-hi nnrat] ['w-lo nnrat] ['s-lo nnrat]
     ['s-hi nnrat] ['b-hi nnrat] ['v nnrat]
     ['lower (at-most 'w-lo (add (mul 'a-lo 'v) 's-lo))]
     ['upper (at-most (add (mul 'a-hi 'v) 's-hi) 'b-hi)]]
    (let [alo-v (mul 'a-lo 'v)
          ahi-v (mul 'a-hi 'v)
          d1 (mul alo-v 'a-hi)          ; (a_lo*v)*a_hi
          d2 (mul ahi-v 'a-lo)          ; (a_hi*v)*a_lo
          wlo-ahi (mul 'w-lo 'a-hi)
          slo-ahi (mul 's-lo 'a-hi)
          shi-alo (mul 's-hi 'a-lo)
          bhi-alo (mul 'b-hi 'a-lo)
          lo-rhs (add alo-v 's-lo)      ; a_lo*v + s_lo
          hi-lhs (add ahi-v 's-hi)      ; a_hi*v + s_hi
          ;; A: w_lo*a_hi <= d1 + s_lo*a_hi
          scale-lo (mul-right-monotone 'w-lo lo-rhs 'a-hi 'lower)
          dist-lo (distribute-right alo-v 's-lo 'a-hi) ; lo-rhs*a_hi ~ d1 + slo-ahi
          proof-a (at-most-respects
                   wlo-ahi wlo-ahi (add d1 slo-ahi) (mul lo-rhs 'a-hi)
                   (erefl wlo-ahi)
                   (esym (mul lo-rhs 'a-hi) (add d1 slo-ahi) dist-lo)
                   scale-lo)
          ;; B: d2 + s_hi*a_lo <= b_hi*a_lo
          scale-hi (mul-right-monotone hi-lhs 'b-hi 'a-lo 'upper)
          dist-hi (distribute-right ahi-v 's-hi 'a-lo) ; hi-lhs*a_lo ~ d2 + shi-alo
          proof-b (at-most-respects
                   (add d2 shi-alo) (mul hi-lhs 'a-lo) bhi-alo bhi-alo
                   (esym (mul hi-lhs 'a-lo) (add d2 shi-alo) dist-hi)
                   (erefl bhi-alo)
                   scale-hi)
          ;; d1 ~ d2 via swap-right + commutative
          swap-lo (mul-swap-right 'a-lo 'v 'a-hi)  ; d1 ~ (a_lo*a_hi)*v
          swap-hi (mul-swap-right 'a-hi 'v 'a-lo)  ; d2 ~ (a_hi*a_lo)*v
          comm-p (mul-respects (mul 'a-lo 'a-hi) (mul 'a-hi 'a-lo) 'v 'v
                               (mul-commutative 'a-lo 'a-hi) (erefl 'v))
          d1-eq-d2 (etrans d1 (mul (mul 'a-lo 'a-hi) 'v) d2
                           swap-lo
                           (etrans (mul (mul 'a-lo 'a-hi) 'v)
                                   (mul (mul 'a-hi 'a-lo) 'v) d2
                                   comm-p
                                   (esym d2 (mul (mul 'a-hi 'a-lo) 'v) swap-hi)))
          ;; B': d1 + s_hi*a_lo <= b_hi*a_lo  (transport B's d2 -> d1)
          proof-b' (at-most-respects
                    (add d1 shi-alo) (add d2 shi-alo) bhi-alo bhi-alo
                    (add-respects d1 d2 shi-alo shi-alo d1-eq-d2 (erefl shi-alo))
                    (erefl bhi-alo)
                    proof-b)]
      ;; hand the two additive rows to the core:
      ;;   w=wlo-ahi, s_lo=slo-ahi, s_hi=shi-alo, b=bhi-alo, v=d1
      (additive-cross wlo-ahi slo-ahi shi-alo bhi-alo d1 proof-a proof-b')))})

(def definition-specs [])
(def theorem-specs [affine-cross-necessary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.farkas-additive-cross rainbow.math.rational.nnrat.multiply-right-monotone rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-affine-cross (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-affine-cross))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
