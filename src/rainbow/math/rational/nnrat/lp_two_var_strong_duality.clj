(ns rainbow.math.rational.nnrat.lp-two-var-strong-duality
  "Brick 5d-iii of the general LP strong-duality Fourier-Motzkin encoding
 : a two-variable strong-duality
  instance whose primal-optimality is proved BY THE FM ENGINE.

  The LP: maximize x1 + 2*x2 subject to x1 + x2 <= 1, x1,x2 >= 0. Its
  optimum is 2, attained at (0,1); the dual (single multiplier y = 2 on the
  binding constraint) has b*y = 2, so the gap is zero. This instance is
  chosen because its optimality genuinely REQUIRES combining the objective
  with the constraint -- it cannot be read off by scaling one constraint --
  so the Fourier-Motzkin cross + both-sides machinery is doing real work,
  not decoration.

  nnrat/lp-two-var-example-primal-optimal proves the primal bound: every
  feasible (x1,x2) has x1 + 2*x2 <= 2. The proof runs the FM elimination of
  x1: the additive cross crux (brick 5c core) against the constraint gives
  (x1+2*x2) + x2 <= 1 + 2*x2 -- x2 on both sides -- which the both-sides
  conversion (brick 5d-ii, difference witness 1+1~2) turns into
  x1+2*x2 <= x2 + 1; then x2 <= 1 (x2 <= x1+x2 <= 1) closes it to
  x1+2*x2 <= 2. First multi-variable LP optimality proved through actual
  variable elimination. Native proof data, axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.farkas-additive-cross :as cross]
            [rainbow.math.rational.nnrat.farkas-both-sides :as both-sides]
            [rainbow.math.rational.nnrat.add-upper :as add-upper]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- mul [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(def one (function/const* 'nnrat/one []))
(def two (add one one))

(defn- erefl [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- esym [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- etrans [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))
(defn- add-commutative [a b]
  (function/app (function/const* 'nnrat/add-commutative []) a b))
(defn- add-respects [left left-eq right right-eq same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left left-eq right right-eq same-left same-right))
(defn- add-right-monotone [addend left right ordered]
  (function/app (function/const* 'nnrat/add-right-monotone [])
                addend left right ordered))
(defn- multiply-one-left [x]
  (function/app (function/const* 'nnrat/multiply-one-left []) x))
(defn- at-most-reflexive [value]
  (function/app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))
(defn- at-most-respects [left eq-left right eq-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left eq-left right eq-right same-left same-right ordered))
(defn- at-most-add-right [a b]
  (function/app (function/const* 'nnrat/at-most-add-right []) a b))
(defn- additive-cross [w s-lo s-hi b v lower upper]
  (function/app (function/const* 'nnrat/farkas-additive-cross-necessary [])
                w s-lo s-hi b v lower upper))
(defn- both-sides-to-lower [a b d p q v diff both]
  (function/app (function/const* 'nnrat/farkas-both-sides-to-lower [])
                a b d p q v diff both))
(def zero (function/const* 'nnrat/zero []))
(defn- equiv [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- add-zero-left [x]
  (function/app (function/const* 'nnrat/add-zero-left []) x))
(defn- multiply-one-right [x]
  (function/app (function/const* 'nnrat/multiply-one-right []) x))
(defn- conjunction [left right]
  (function/app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))

(def primal-optimal-spec
  {:name 'nnrat/lp-two-var-example-primal-optimal
   :universes []
   :type
   (function/forall
    [['x1 nnrat] ['x2 nnrat]
     ['feasible (at-most (add 'x1 'x2) one)]]
    (at-most (add 'x1 (mul two 'x2)) two))
   :value
   (function/lam
    [['x1 nnrat] ['x2 nnrat]
     ['feasible (at-most (add 'x1 'x2) one)]]
    (let [twx2 (mul two 'x2)
          obj (add 'x1 twx2)
          onex2 (mul one 'x2)
          ;; eliminate x1 via the additive cross crux against the constraint.
          ;; lower row: obj <= x1 + 2*x2 is reflexive (obj IS x1 + 2*x2).
          cross (additive-cross obj twx2 'x2 one 'x1
                                (at-most-reflexive obj) 'feasible)
          ;; cross : (obj + x2) <= (one + 2*x2)
          ;; recast to A*x2+P <= B*x2+Q form: (1*x2 + obj) <= (2*x2 + one)
          lhs-eq (etrans (add obj 'x2) (add 'x2 obj) (add onex2 obj)
                         (add-commutative obj 'x2)
                         (add-respects 'x2 onex2 obj obj
                                       (esym onex2 'x2 (multiply-one-left 'x2))
                                       (erefl obj)))
          rhs-eq (add-commutative one twx2)
          cross' (at-most-respects
                  (add onex2 obj) (add obj 'x2)
                  (add twx2 one) (add one twx2)
                  (esym (add obj 'x2) (add onex2 obj) lhs-eq)
                  (esym (add one twx2) (add twx2 one) rhs-eq)
                  cross)
          ;; both-sides -> affine lower: obj <= 1*x2 + one   (D = one, 1+1~2)
          lower-row (both-sides-to-lower one two one obj one 'x2
                                         (erefl (add one one)) cross')
          ;; recast 1*x2 -> x2 : obj <= x2 + one
          obj-le (at-most-respects
                  obj obj (add 'x2 one) (add onex2 one)
                  (erefl obj)
                  (add-respects 'x2 onex2 one one
                                (esym onex2 'x2 (multiply-one-left 'x2))
                                (erefl one))
                  lower-row)
          ;; x2 <= x1 + x2 <= 1
          x2-le-sum (at-most-respects
                     'x2 'x2 (add 'x1 'x2) (add 'x2 'x1)
                     (erefl 'x2)
                     (add-commutative 'x1 'x2)
                     (at-most-add-right 'x2 'x1))
          x2-le-one (at-most-transitive 'x2 (add 'x1 'x2) one x2-le-sum 'feasible)
          ;; x2 + one <= one + one = two
          x2one-le-two (add-right-monotone one 'x2 one x2-le-one)]
      ;; obj <= x2 + one <= two
      (at-most-transitive obj (add 'x2 one) two obj-le x2one-le-two)))})

;; Strong duality: the FM bound 2 is TIGHT. The optimal point x* = (0,1) is
;; feasible and attains x1 + 2*x2 = 2, and the dual y = 2 on the binding
;; constraint gives b*y = 1*2 = 2 -- so primal optimum = dual optimum = 2,
;; zero gap. Together with lp-two-var-example-primal-optimal (every feasible
;; point <= 2), this is strong duality for the two-variable LP.
(def strong-duality-spec
  {:name 'nnrat/lp-two-var-example-strong-duality
   :universes []
   :type
   (conjunction
    (at-most (add zero one) one)                       ; (0,1) feasible
    (conjunction
     (equiv (add zero (mul two one)) two)              ; obj(0,1) ~ 2 (bound attained)
     (equiv (mul one two) two)))                       ; dual b*y = 1*2 ~ 2 (zero gap)
   :value
   (let [obj-star (add zero (mul two one))
         value-star-prop (equiv obj-star two)
         dual-prop (equiv (mul one two) two)
         ;; (0,1) feasible: 0 + 1 ~ 1 <= 1
         feasible-star
         (at-most-respects (add zero one) one one one
                           (add-zero-left one) (erefl one)
                           (at-most-reflexive one))
         ;; obj(0,1) = 0 + 2*1 ~ 0 + 2 ~ 2
         value-star
         (etrans obj-star (add zero two) two
                 (add-respects zero zero (mul two one) two
                               (erefl zero) (multiply-one-right two))
                 (add-zero-left two))
         ;; dual b*y = 1*2 ~ 2
         dual (multiply-one-left two)]
     (conjoin (at-most (add zero one) one)
              (conjunction value-star-prop dual-prop)
              feasible-star
              (conjoin value-star-prop dual-prop value-star dual)))})

(def definition-specs [])
(def theorem-specs [primal-optimal-spec strong-duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      cross/extend-environment
      both-sides/extend-environment
      add-upper/extend-environment
      (support/extend-with :nnrat-lp-two-var-strong-duality
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
