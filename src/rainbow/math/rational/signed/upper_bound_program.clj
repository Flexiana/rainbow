(ns rainbow.math.rational.signed.upper-bound-program
  "A worked constrained program, certified end-to-end by the general duality
  theorem -- the non-vacuity witness for the signed Lagrangian stack.

  For an ARBITRARY signed bound c, take the one-constraint program

      minimize   f y  = -y            (equivalently: maximize y)
      subject to g y  = y - c <= 0    (equivalently: y <= c)

  and relax it with the single multiplier lambda = 1.  The Lagrangian collapses
  to a constant:

      L y  =  -y + 1*(y - c)  ~  -c

  so the dual value -c bounds L everywhere, which is exactly the `bound`
  hypothesis of `optimization/signed-constrained-weak-duality`.  The remaining
  hypotheses are the new unit laws: 0 <= 1 gives multiplier nonnegativity,
  c - c <= 0 gives feasibility of the candidate x0 = c, and the zero gap is
  reflexivity because f c is literally -c.

  Feeding all of that to `optimization/signed-constrained-zero-gap-optimal`
  yields, for every c and every x in the feasible set,

      optimization/signed-upper-bound-program-optimal :  x - c <= 0  ->  -c <= -x

  i.e. c maximizes the objective subject to x <= c.  The conclusion is elementary
  on its own; the point is that it is DERIVED, for a whole parameterized family,
  through the abstract weak-duality / zero-gap machinery rather than proved
  directly -- so that machinery is inhabited, not vacuous.

  The one piece of real work is the Lagrangian collapse: over Grothendieck pairs
  it is the nnrat reassociation
  `Nc + (Py + (Ny + Pc)) ~ (Ny + (Py + Nc)) + Pc`, both sides being the same
  four-element multiset -- one `rainbow.math.rational.nnrat.ring` call.

  Native and axiom-free; chains the concrete constrained-duality module, the
  signed unit laws, the KKT congruence and the nnrat-ring tactic on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.constrained-duality :as constrained]
            [rainbow.math.rational.signed.kkt-sufficiency :as kkt]
            [rainbow.math.rational.signed.unit-laws :as unit]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sneg [v] (app (function/const* 'signed/negate []) v))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))

(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
;; signed equivalence IS the nnrat equivalence of the two cross sums, so nnrat
;; symmetry is a signed symmetry proof.
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- signed-add-left-respects [a b c same]
  (app (function/const* 'signed/add-left-respects-equivalence []) a b c same))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))
(defn- signed-multiply-one-left [v]
  (app (function/const* 'signed/multiply-one-left []) v))
(defn- signed-equivalent-to-at-most [a b same]
  (app (function/const* 'signed/equivalent-to-at-most []) a b same))

;; ---- the program's data ------------------------------------------------------

(def index-list
  (app (function/const* 'data/cons [type-level]) nat
       (function/const* 'data/zero [])
       (app (function/const* 'data/nil [type-level]) nat)))

(defn- objective [] (function/lam [['y signed]] (sneg 'y)))
(defn- multipliers [] (function/lam [['i nat]] signed-one))
(defn- constraints [c]
  (function/lam [['i nat]] (function/lam [['y signed]] (ssub 'y c))))
(defn- feasible [c]
  (function/lam [['y signed]] (sle (ssub 'y c) signed-zero)))

;; ---- the Lagrangian collapse -------------------------------------------------

;; -c ~ (-y) + (y - c).  Componentwise this is
;;   Nc + (Py + (Ny + Pc))  ~  (Ny + (Py + Nc)) + Pc,
;; the same four summands on both sides in different bracketings.
(def lagrangian-collapse-spec
  {:name 'optimization/signed-upper-bound-lagrangian-collapse :universes []
   :type (function/forall
          [['c signed] ['y signed]]
          (seq-equiv (sneg 'c) (sadd (sneg 'y) (ssub 'y 'c))))
   :value
   (function/lam
    [['c signed] ['y signed]]
    ;; the four summands are the same on both sides; one normalization
    (ring/equiv (radd (neg 'c) (radd (pos 'y) (radd (neg 'y) (pos 'c))))
                (radd (radd (neg 'y) (radd (pos 'y) (neg 'c))) (pos 'c))))})

;; The `bound` hypothesis of the general theorem, discharged for this program:
;; the dual value -c is below the Lagrangian at every point.  Three rewrites take
;; -c through the collapse, then re-introduce the multiplier and the empty tail
;; of the one-element sum.
(def dual-bound-spec
  {:name 'optimization/signed-upper-bound-dual-bound :universes []
   :type (function/forall
          [['c signed] ['y signed]]
          (sle (sneg 'c)
               (sadd (sneg 'y)
                     (sadd (smul signed-one (ssub 'y 'c)) signed-zero))))
   :value
   (function/lam
    [['c signed] ['y signed]]
    (let [base (sneg 'c)
          raw (sadd (sneg 'y) (ssub 'y 'c))
          scaled (sadd (sneg 'y) (smul signed-one (ssub 'y 'c)))
          padded (sadd (sneg 'y)
                       (sadd (smul signed-one (ssub 'y 'c)) signed-zero))
          collapse (app (function/const*
                         'optimization/signed-upper-bound-lagrangian-collapse [])
                        'c 'y)
          ;; -c <= (-y) + (y - c)
          step-one (signed-equivalent-to-at-most base raw collapse)
          ;; ... <= (-y) + 1*(y - c)
          step-two
          (signed-at-most-respects
           base base raw scaled
           (signed-refl base)
           (signed-add-left-respects
            (ssub 'y 'c) (smul signed-one (ssub 'y 'c)) (sneg 'y)
            (signed-sym (smul signed-one (ssub 'y 'c)) (ssub 'y 'c)
                        (signed-multiply-one-left (ssub 'y 'c))))
           step-one)]
      ;; ... <= (-y) + (1*(y - c) + 0), which is the one-element penalty sum
      (signed-at-most-respects
       base base scaled padded
       (signed-refl base)
       (signed-add-left-respects
        (smul signed-one (ssub 'y 'c))
        (sadd (smul signed-one (ssub 'y 'c)) signed-zero)
        (sneg 'y)
        (signed-sym (sadd (smul signed-one (ssub 'y 'c)) signed-zero)
                    (smul signed-one (ssub 'y 'c))
                    (signed-add-zero-right (smul signed-one (ssub 'y 'c)))))
       step-two)))})

;; ---- the certified optimum ---------------------------------------------------

(def program-optimal-spec
  {:name 'optimization/signed-upper-bound-program-optimal :universes []
   :type (function/forall
          [['c signed] ['x signed]
           ['member (sle (ssub 'x 'c) signed-zero)]]
          (sle (sneg 'c) (sneg 'x)))
   :value
   (function/lam
    [['c signed] ['x signed]
     ['member (sle (ssub 'x 'c) signed-zero)]]
    (app (function/const*
          'optimization/signed-constrained-zero-gap-optimal [zero-level])
         nat
         (objective)
         (multipliers)
         (constraints 'c)
         index-list
         (feasible 'c)
         (sneg 'c)
         ;; bound
         (function/lam
          [['y signed]]
          (app (function/const* 'optimization/signed-upper-bound-dual-bound [])
               'c 'y))
         ;; nonnegative multipliers
         (function/lam [['i nat]]
                       (function/const* 'signed/zero-at-most-one []))
         ;; feasibility of a feasible point is literally the constraint
         (function/lam
          [['y signed] ['member-y (sle (ssub 'y 'c) signed-zero)]
           ['i nat]]
          'member-y)
         ;; the candidate x0 = c, feasible because c - c <= 0
         'c
         (app (function/const* 'signed/subtract-self-nonpositive []) 'c)
         ;; zero gap: the dual value IS the objective at c
         (signed-refl (sneg 'c))
         'x 'member))})

(def definition-specs [])
(def theorem-specs
  [lagrangian-collapse-spec dual-bound-spec program-optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      constrained/extend-environment
      kkt/extend-environment
      unit/extend-environment
      ring/extend-environment
      (support/extend-with :signed-upper-bound-program theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
