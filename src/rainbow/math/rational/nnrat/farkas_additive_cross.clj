(ns rainbow.math.rational.nnrat.farkas-additive-cross
  "Brick 5c core of the general LP strong-duality Fourier-Motzkin encoding
 : the additive cross-elimination
  crux -- the necessary (certificate) direction, coefficient-1 case.

  This is the heart of the affine cross-product the payoff needs. Eliminating
  a variable v that is bounded below by one affine row and above by another,
  the FM condition on the survivors is that the lower's slack plus the
  upper's block does not exceed the upper's bound plus the lower's block.
  In the coefficient-1 case: from w <= v + s_lo (lower) and v + s_hi <= b
  (upper), the surviving condition is w + s_hi <= b + s_lo -- the additive
  cross condition, with v eliminated.

  This is the NECESSARY direction (any feasible v yields the cross
  condition); its contrapositive is the infeasibility certificate that
  becomes the dual once the objective bound exceeds the optimum. Proof:
  add s_hi to the lower row and s_lo to the upper row, reassociate the
  middle term (v + s_lo) + s_hi ~ (v + s_hi) + s_lo up to nnrat
  equivalence, and chain by transitivity. Positivity-free (no coefficients
  yet). The coefficient wrapper -- scale each row by the other's
  coefficient (multiply-right-monotone), distribute
  (multiply-distributes-add-right), and align the products
  (multiply-swap-right) down to this additive core -- is the follow-on
  brick. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as reassoc]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- add-associative [a b c]
  (function/app (function/const* 'nnrat/add-associative []) a b c))
(defn- add-commutative [a b]
  (function/app (function/const* 'nnrat/add-commutative []) a b))
(defn- add-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- add-right-monotone [addend left right ordered]
  (function/app (function/const* 'nnrat/add-right-monotone [])
                addend left right ordered))
(defn- at-most-respects [left eq-left right eq-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left eq-left right eq-right same-left same-right ordered))
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))

(def additive-cross-necessary-spec
  {:name 'nnrat/farkas-additive-cross-necessary
   :universes []
   :type
   (function/forall
    [['w nnrat] ['s-lo nnrat] ['s-hi nnrat] ['b nnrat] ['v nnrat]
     ['lower (at-most 'w (add 'v 's-lo))]
     ['upper (at-most (add 'v 's-hi) 'b)]]
    (at-most (add 'w 's-hi) (add 'b 's-lo)))
   :value
   (function/lam
    [['w nnrat] ['s-lo nnrat] ['s-hi nnrat] ['b nnrat] ['v nnrat]
     ['lower (at-most 'w (add 'v 's-lo))]
     ['upper (at-most (add 'v 's-hi) 'b)]]
    (let [w+shi (add 'w 's-hi)
          v+slo (add 'v 's-lo)
          v+shi (add 'v 's-hi)
          mid-lo (add v+slo 's-hi)     ; (v + s_lo) + s_hi
          mid-hi (add v+shi 's-lo)     ; (v + s_hi) + s_lo
          b+slo (add 'b 's-lo)
          ;; A: w + s_hi <= (v + s_lo) + s_hi
          step-a (add-right-monotone 's-hi 'w v+slo 'lower)
          ;; reassociate the middle: (v+s_lo)+s_hi ~ (v+s_hi)+s_lo
          e1 (add-associative 'v 's-lo 's-hi)        ; mid-lo ~ v+(s_lo+s_hi)
          e2 (add-respects 'v 'v (add 's-lo 's-hi) (add 's-hi 's-lo)
                           (equivalent-reflexive 'v)
                           (add-commutative 's-lo 's-hi)) ; v+(s_lo+s_hi) ~ v+(s_hi+s_lo)
          e3 (equivalent-symmetric mid-hi (add 'v (add 's-hi 's-lo))
                                   (add-associative 'v 's-hi 's-lo)) ; v+(s_hi+s_lo) ~ mid-hi
          reassoc (equivalent-transitive
                   mid-lo (add 'v (add 's-lo 's-hi)) mid-hi
                   e1 (equivalent-transitive
                       (add 'v (add 's-lo 's-hi)) (add 'v (add 's-hi 's-lo)) mid-hi
                       e2 e3))
          ;; A'': w + s_hi <= (v + s_hi) + s_lo  (transport A's right endpoint)
          step-a'' (at-most-respects
                    w+shi w+shi mid-hi mid-lo
                    (equivalent-reflexive w+shi)
                    (equivalent-symmetric mid-lo mid-hi reassoc)
                    step-a)
          ;; B: (v + s_hi) + s_lo <= b + s_lo
          step-b (add-right-monotone 's-lo v+shi 'b 'upper)]
      ;; chain: w + s_hi <= (v+s_hi)+s_lo <= b + s_lo
      (at-most-transitive w+shi mid-hi b+slo step-a'' step-b)))})

(def definition-specs [])
(def theorem-specs [additive-cross-necessary-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-monotone/extend-environment
      reassoc/extend-environment
      (support/extend-with :nnrat-farkas-additive-cross
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
