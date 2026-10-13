(ns rainbow.algorithms.proofs.ahof.lqr
  "LQR linear feedback control (Kochenderfer Decision Making D7.11), one of
  the signed-subtraction cluster deferred in August until the signed layer
  landed.

  The control law is the linear feedback u = -K x: negate the gain-scaled
  state. `control/lqr-action gain state = signed/negate (signed/scale gain
  state)`, a higher-order composition of the two signed primitives, and the
  worked theorem proves the concrete action for gain 2, state 3 is
  equivalent to -6 by signed cross-product reflexivity -- the standard
  worked-instance idiom of the 222 catalog. Native and axiom-free on D63;
  a proved native module at module level, not a formally credited ledger
  row (that pipeline is a separate follow-up per the catalog workflow)."
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.counterfactual-objective-laws :as scale-sign]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.deviation-rows :as order-reverse]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- numeral [n]
  (loop [remaining (long n) term (function/const* 'data/zero [])]
    (if (zero? remaining)
      term
      (recur (dec remaining) (app (function/const* 'data/succ []) term)))))
(defn- nnrat-of [n]
  (app (function/const* 'nnrat/make []) (numeral n) (function/const* 'data/zero [])))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- signed-scale [gain state]
  (app (function/const* 'signed/scale []) gain state))
(defn- signed-negate [v] (app (function/const* 'signed/negate []) v))
(defn- signed-positive [v] (app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (app (function/const* 'signed/negative []) v))
(defn- nnrat-add [a b] (app (function/const* 'nnrat/add []) a b))
(defn- numerator [v] (app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [a b] (app (function/const* 'nat/multiply []) a b))

(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))

;; signed/equivalent left right unfolds to Eq nat over the Grothendieck
;; cross sums; reflexivity on the numerator*denominator cross term proves a
;; worked value.
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (app (function/const* 'equality/reflexive [type-level])
         nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def lqr-action-spec
  {:name 'control/lqr-action :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow nnrat signed signed)
   :value (function/lam
           [['gain nnrat] ['state signed]]
           (signed-negate (signed-scale 'gain 'state)))})

(defn- lqr-action [gain state]
  (app (function/const* 'control/lqr-action []) gain state))

(def lqr-action-worked-spec
  "Worked instance: gain 2 applied to state 3 yields action equivalent to
  -6, the linear feedback -K x for K=2, x=3."
  {:name 'control/lqr-action-worked :universes []
   :type (signed-equivalent
          (lqr-action (nnrat-of 2) (from-nnrat (nnrat-of 3)))
          (signed-negate (from-nnrat (nnrat-of 6))))
   :value (signed-equivalent-cross
           (lqr-action (nnrat-of 2) (from-nnrat (nnrat-of 3)))
           (signed-negate (from-nnrat (nnrat-of 6))))})

(defn- signed-nonnegative [v] (app (function/const* 'signed/nonnegative []) v))
(defn- signed-at-most [a b] (app (function/const* 'signed/at-most []) a b))
(defn- signed-scale [g v] (app (function/const* 'signed/scale []) g v))
(defn- signed-zero [] (function/const* 'signed/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(def lqr-action-sign-reversing-spec
  "The UNIVERSAL structural property that makes -Kx a stabilizing
  feedback rather than an arithmetic identity: for every gain and every
  NONNEGATIVE state, the action is NONPOSITIVE -- the control opposes the
  state. Proof: the gain-scaled nonnegative state is nonnegative, and
  negation reverses the order, so the negated scale sits at most zero
  (transporting negate-zero on the right)."
  {:name 'control/lqr-action-sign-reversing :universes []
   :type (function/forall
          [['gain nnrat] ['state signed]
           ['state-nonnegative (signed-nonnegative 'state)]]
          (signed-at-most (lqr-action 'gain 'state) (signed-zero)))
   :value
   (function/lam
    [['gain nnrat] ['state signed]
     ['state-nonnegative (signed-nonnegative 'state)]]
    (let [scaled (signed-scale 'gain 'state)
          scale-nonneg (app (function/const* 'signed/scale-nonnegative [])
                            'gain 'state 'state-nonnegative)
          zero-at-most-scaled
          (app (function/const* 'signed/zero-at-most-of-nonnegative [])
               scaled scale-nonneg)
          reversed (app (function/const* 'signed/negate-reverses-order [])
                        (signed-zero) scaled zero-at-most-scaled)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           (signed-negate scaled) (signed-negate scaled)
           (signed-zero) (signed-negate (signed-zero))
           (app (function/const* 'signed/equivalent-reflexive [])
                (signed-negate scaled))
           (app (function/const* 'signed/equivalent-symmetric [])
                (signed-negate (signed-zero)) (signed-zero)
                (function/const* 'signed/negate-zero []))
           reversed)))})

(def definition-specs [lqr-action-spec])
(def theorem-specs [lqr-action-worked-spec lqr-action-sign-reversing-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.counterfactual-objective-laws rainbow.math.rational.signed.deviation-rows])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :ahof-lqr (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.algorithms.proofs.ahof.lqr))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
