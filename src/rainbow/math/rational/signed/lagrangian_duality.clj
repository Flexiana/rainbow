(ns rainbow.math.rational.signed.lagrangian-duality
  "Lagrangian duality for general constrained optimization over signed rationals.

  A constrained program `minimize f x subject to x feasible` is relaxed by
  moving the constraints into the objective with nonnegative multipliers:

      L y = f y + penalty y,        penalty y = sum_i lambda_i * g_i y.

  Two facts characterize the relaxation, and both are taken as hypotheses so
  that no signed multiplication or constraint-list representation has to be
  postulated here:

    * `bound`      -- the dual value is a lower bound of the Lagrangian
                      everywhere: dual-value <= f y + penalty y for every y.
                      (This is what `dual-value <= inf_y L y` means.)
    * `slack`      -- on the feasible set the penalty is never a bonus:
                      penalty x <= 0.  Over a real program this is exactly
                      lambda_i >= 0 together with g_i x <= 0.

  From these three theorems follow.

    WEAK DUALITY            dual-value <= f x for every feasible x, so every
                            dual value certifies a lower bound on the primal
                            optimum -- the reason a branch-and-bound node may
                            be pruned, and the reason a relaxation is sound.

    ZERO-GAP OPTIMALITY     if some feasible x0 attains the dual value, it is a
                            global primal minimizer.  This is the certificate a
                            solver emits: a primal point plus a dual value that
                            match.

    COMPLEMENTARY SLACKNESS at such a zero-gap pair the penalty vanishes:
                            penalty x0 ~ 0.  Every active multiplier sits on an
                            active constraint.

  This generalizes the nnrat LP duality stack to arbitrary signed objectives:
  nothing here assumes linearity, only order.  Native and axiom-free; chains
  signed limit uniqueness (add-zero-right, antisymmetry), signed order
  monotonicity and signed order cancellation on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.order-cancellation :as cancellation]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def signed (function/const* 'signed/SignedRational []))
(def objective (function/arrow signed signed))
(def predicate (function/arrow signed 'Prop))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-transitive [a b c ab bc]
  (app (function/const* 'signed/at-most-transitive []) a b c ab bc))
(defn- signed-antisymmetric [a b ab ba]
  (app (function/const* 'signed/at-most-antisymmetric []) a b ab ba))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-add-left-monotone [a b c ordered]
  (app (function/const* 'signed/add-left-monotone []) a b c ordered))
(defn- signed-add-left-cancel [a b c ordered]
  (app (function/const* 'signed/at-most-add-left-cancel []) a b c ordered))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))

;; Signed equivalence is an nnrat equivalence between the two cross sums, so it
;; inherits symmetry definitionally -- no new alias is introduced for it.
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))

;; A hypothesis shared by every theorem below: the dual value underestimates the
;; Lagrangian everywhere.
(defn- bound-type [f penalty dual]
  (function/forall [['y signed]]
                   (sle dual (sadd (app f 'y) (app penalty 'y)))))

;; And: on the feasible set the penalty is nonpositive.
(defn- slack-type [penalty feasible]
  (function/forall [['y signed] ['member (app feasible 'y)]]
                   (sle (app penalty 'y) signed-zero)))

;; The Lagrangian at a feasible point never exceeds the objective there:
;; f x + penalty x <= f x + 0 ~ f x.
(defn- lagrangian-below-objective [f penalty slack x member]
  (let [fx (app f x)
        px (app penalty x)
        relaxed (sadd fx px)
        padded (sadd fx signed-zero)]
    (signed-at-most-respects
     relaxed relaxed padded fx
     (signed-refl relaxed)
     (signed-add-zero-right fx)
     (signed-add-left-monotone px signed-zero fx (app slack x member)))))

(def weak-duality-spec
  {:name 'optimization/signed-lagrangian-weak-duality :universes []
   :type
   (function/forall
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle 'dual (app 'f 'x)))
   :value
   (function/lam
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x signed] ['member (app 'feasible 'x)]]
    (signed-transitive
     'dual (sadd (app 'f 'x) (app 'penalty 'x)) (app 'f 'x)
     (app 'bound 'x)
     (lagrangian-below-objective 'f 'penalty 'slack 'x 'member)))})

;; A feasible point attaining the dual value is a global minimizer: weak duality
;; bounds every feasible objective value from below by the dual value, and the
;; zero gap identifies that bound with f x0.
(def zero-gap-optimal-spec
  {:name 'optimization/signed-lagrangian-zero-gap-primal-optimal :universes []
   :type
   (function/forall
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]
     ['x signed] ['member (app 'feasible 'x)]]
    (sle (app 'f 'x0) (app 'f 'x)))
   :value
   (function/lam
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]
     ['x signed] ['member (app 'feasible 'x)]]
    (signed-at-most-respects
     'dual (app 'f 'x0) (app 'f 'x) (app 'f 'x)
     'gap (signed-refl (app 'f 'x))
     (app (function/const* 'optimization/signed-lagrangian-weak-duality [])
          'f 'penalty 'feasible 'dual 'bound 'slack 'x 'member)))})

;; At a zero-gap pair the penalty vanishes.  The Lagrangian lower bound at x0
;; becomes f x0 + 0 <= f x0 + penalty x0 once the gap is closed and the padding
;; is inserted; cancelling the shared f x0 leaves 0 <= penalty x0, and the
;; feasibility slack gives the opposite inequality.
(def complementary-slackness-spec
  {:name 'optimization/signed-lagrangian-complementary-slackness :universes []
   :type
   (function/forall
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]]
    (seq-equiv (app 'penalty 'x0) signed-zero))
   :value
   (function/lam
    [['f objective] ['penalty objective] ['feasible predicate]
     ['dual signed]
     ['bound (bound-type 'f 'penalty 'dual)]
     ['slack (slack-type 'penalty 'feasible)]
     ['x0 signed] ['x0-member (app 'feasible 'x0)]
     ['gap (seq-equiv 'dual (app 'f 'x0))]]
    (let [f0 (app 'f 'x0)
          p0 (app 'penalty 'x0)
          relaxed (sadd f0 p0)
          padded (sadd f0 signed-zero)
          ;; f x0 <= f x0 + penalty x0
          objective-below-relaxed
          (signed-at-most-respects
           'dual f0 relaxed relaxed
           'gap (signed-refl relaxed)
           (app 'bound 'x0))
          ;; re-insert the padding so the shared summand is syntactically there
          padded-below-relaxed
          (signed-at-most-respects
           f0 padded relaxed relaxed
           (signed-sym padded f0 (signed-add-zero-right f0))
           (signed-refl relaxed)
           objective-below-relaxed)
          zero-below-penalty
          (signed-add-left-cancel signed-zero p0 f0 padded-below-relaxed)]
      (signed-antisymmetric p0 signed-zero
                            (app 'slack 'x0 'x0-member)
                            zero-below-penalty)))})

(def definition-specs [])
(def theorem-specs
  [weak-duality-spec zero-gap-optimal-spec complementary-slackness-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniqueness/extend-environment
      monotone/extend-environment
      cancellation/extend-environment
      (support/extend-with :signed-lagrangian-duality theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
